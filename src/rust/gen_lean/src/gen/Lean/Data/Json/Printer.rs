// Lean compiler output
// Module: Lean.Data.Json.Printer
// Imports: Lean.Data.Format Lean.Data.Json.Basic Init.Data.String.Search Init.Data.UInt.Lemmas Init.Omega
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_pretty;
use crate::r#gen::Init::Data::Repr::l_Nat_digitChar;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Lean::Data::Format::{
    initialize_Lean_Data_Format, runtime_initialize_Lean_Data_Format,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    initialize_Lean_Data_Json_Basic, l_Lean_JsonNumber_toString,
    runtime_initialize_Lean_Data_Json_Basic,
};
use crate::ffi::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_byte_array_fget;
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::ffi::{lean_string_length, lean_string_push};
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_get_byte_fast;
use crate::ffi::{
    lean_uint8_to_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_mod, lean_nat_sub, lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_to_nat, lean_usize_dec_eq,
};
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0_value:
    crate::leanh::LeanScalarArray<256> = crate::leanh::LeanScalarArray {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + 256) as u16,
        other: 1,
        tag: 248,
    },
    m_size: 256,
    m_capacity: 256,
    m_data: [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    ],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0_value:
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
    m_data: [92, 117, 0],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1_value:
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
    m_data: [92, 114, 0],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2_value:
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
    m_data: [92, 110, 0],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3_value:
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
    m_data: [92, 92, 0],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4_value:
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
    m_data: [92, 34, 0],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_renderString___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [34, 0],
    };
static mut l_Lean_Json_renderString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_renderString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Json_render___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Json_render___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Json_render___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__6_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Json_render___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__6_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Json_render___closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_render___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__9_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lean_Json_render___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json_render___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_render___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_render___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_render___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_render___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__9_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__10_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Json_render___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__14_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__10_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__15_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [123, 0],
    };
static mut l_Lean_Json_render___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Json_render___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_render___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Json_render___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_render___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_render___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__15_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__16_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [125, 0],
    };
static mut l_Lean_Json_render___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_render___closed__20_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lean_Json_render___closed__16_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_render___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_render___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0_value:
    crate::leanh::LeanArrayObject<2> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        (((5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1_value:
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
static mut l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_compress___closed__0_value: crate::leanh::LeanArrayObject<1> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Json_compress___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_compress___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instToFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_render as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instToFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instToFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(
    mut v_acc_1882_: *mut crate::leanh::LeanObject,
    mut v_c_1883_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d1_1889_: u32 = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d2_1894_: u32 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d3_1899_: u32 = 0;
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d4_1901_: u32 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u32 = 0;
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: u32 = 0;
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: u32 = 0;
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: u32 = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: u32 = 0;
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: u32 = 0;
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1908_ = 34;
                v___x_1909_ = lean_uint32_dec_eq(v_c_1883_, v___x_1908_);
                if v___x_1909_ == 0 {
                    v___x_1910_ = 92;
                    v___x_1911_ = lean_uint32_dec_eq(v_c_1883_, v___x_1910_);
                    if v___x_1911_ == 0 {
                        v___x_1912_ = 10;
                        v___x_1913_ = lean_uint32_dec_eq(v_c_1883_, v___x_1912_);
                        if v___x_1913_ == 0 {
                            v___x_1914_ = 13;
                            v___x_1915_ = lean_uint32_dec_eq(v_c_1883_, v___x_1914_);
                            if v___x_1915_ == 0 {
                                v___x_1916_ = 32;
                                v___x_1917_ = lean_uint32_dec_le(v___x_1916_, v_c_1883_);
                                if v___x_1917_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1918_ = 1114111;
                                    v___x_1919_ = lean_uint32_dec_le(v_c_1883_, v___x_1918_);
                                    if v___x_1919_ == 0 {
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1920_ = lean_string_push(v_acc_1882_, v_c_1883_);
                                        return v___x_1920_;
                                    }
                                }
                            } else {
                                v___x_1921_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__1;
                                v___x_1922_ = lean_string_append(v_acc_1882_, v___x_1921_);
                                return v___x_1922_;
                            }
                        } else {
                            v___x_1923_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__2;
                            v___x_1924_ = lean_string_append(v_acc_1882_, v___x_1923_);
                            return v___x_1924_;
                        }
                    } else {
                        v___x_1925_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__3;
                        v___x_1926_ = lean_string_append(v_acc_1882_, v___x_1925_);
                        return v___x_1926_;
                    }
                } else {
                    v___x_1927_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__4;
                    v___x_1928_ = lean_string_append(v_acc_1882_, v___x_1927_);
                    return v___x_1928_;
                }
            }
            1 => {
                v_n_1885_ = lean_uint32_to_nat(v_c_1883_);
                v___x_1886_ = crate::leanh::lean_unsigned_to_nat(4096);
                v___x_1887_ = crate::leanh::lean_unsigned_to_nat(12);
                v___x_1888_ = lean_nat_shiftr(v_n_1885_, v___x_1887_);
                v_d1_1889_ = l_Nat_digitChar(v___x_1888_);
                crate::leanh::lean_dec(v___x_1888_);
                v___x_1890_ = lean_nat_mod(v_n_1885_, v___x_1886_);
                v___x_1891_ = crate::leanh::lean_unsigned_to_nat(256);
                v___x_1892_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_1893_ = lean_nat_shiftr(v___x_1890_, v___x_1892_);
                crate::leanh::lean_dec(v___x_1890_);
                v_d2_1894_ = l_Nat_digitChar(v___x_1893_);
                crate::leanh::lean_dec(v___x_1893_);
                v___x_1895_ = lean_nat_mod(v_n_1885_, v___x_1891_);
                v___x_1896_ = crate::leanh::lean_unsigned_to_nat(16);
                v___x_1897_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1898_ = lean_nat_shiftr(v___x_1895_, v___x_1897_);
                crate::leanh::lean_dec(v___x_1895_);
                v_d3_1899_ = l_Nat_digitChar(v___x_1898_);
                crate::leanh::lean_dec(v___x_1898_);
                v___x_1900_ = lean_nat_mod(v_n_1885_, v___x_1896_);
                crate::leanh::lean_dec(v_n_1885_);
                v_d4_1901_ = l_Nat_digitChar(v___x_1900_);
                crate::leanh::lean_dec(v___x_1900_);
                v___x_1902_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___closed__0;
                v___x_1903_ = lean_string_append(v_acc_1882_, v___x_1902_);
                v___x_1904_ = lean_string_push(v___x_1903_, v_d1_1889_);
                v___x_1905_ = lean_string_push(v___x_1904_, v_d2_1894_);
                v___x_1906_ = lean_string_push(v___x_1905_, v_d3_1899_);
                v___x_1907_ = lean_string_push(v___x_1906_, v_d4_1901_);
                return v___x_1907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(
    mut v_acc_1929_: *mut crate::leanh::LeanObject,
    mut v_c_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1931_: u32 = 0;
    let mut v_res_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1931_ = crate::leanh::lean_unbox_uint32(v_c_1930_);
    crate::leanh::lean_dec(v_c_1930_);
    v_res_1932_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_1929_, v_c_boxed_1931_);
    return v_res_1932_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(
    mut v_s_1933_: *mut crate::leanh::LeanObject,
    mut v_i_1934_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: u8 = 0;
    let mut v_byte_1937_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1935_ = lean_string_utf8_byte_size(v_s_1933_);
                v___x_1936_ = lean_nat_dec_lt(v_i_1934_, v___x_1935_);
                if v___x_1936_ == 0 {
                    crate::leanh::lean_dec(v_i_1934_);
                    return v___x_1936_;
                } else {
                    crate::leanh::lean_inc(v_i_1934_);
                    v_byte_1937_ = lean_string_get_byte_fast(v_s_1933_, v_i_1934_);
                    v___x_1938_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable;
                    v___x_1939_ = lean_uint8_to_nat(v_byte_1937_);
                    v___x_1940_ = lean_byte_array_fget(v___x_1938_, v___x_1939_);
                    v___x_1941_ = 0;
                    v___x_1942_ = lean_uint8_dec_eq(v___x_1940_, v___x_1941_);
                    if v___x_1942_ == 0 {
                        crate::leanh::lean_dec(v_i_1934_);
                        return v___x_1936_;
                    } else {
                        v___x_1943_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1944_ = lean_nat_add(v_i_1934_, v___x_1943_);
                        crate::leanh::lean_dec(v_i_1934_);
                        v_i_1934_ = v___x_1944_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(
    mut v_s_1946_: *mut crate::leanh::LeanObject,
    mut v_i_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1948_: u8 = 0;
    let mut v_r_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_1946_, v_i_1947_);
    crate::leanh::lean_dec_ref(v_s_1946_);
    v_r_1949_ = crate::leanh::lean_box((v_res_1948_) as usize);
    return v_r_1949_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(
    mut v_s_1950_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    v___x_1951_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1952_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(v_s_1950_, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(
    mut v_s_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1954_: u8 = 0;
    let mut v_r_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1953_);
    crate::leanh::lean_dec_ref(v_s_1953_);
    v_r_1955_ = crate::leanh::lean_box((v_res_1954_) as usize);
    return v_r_1955_;
}
pub unsafe fn l_Lean_Json_escape___lam__0(
    mut v___x_1956_: *mut crate::leanh::LeanObject,
    mut v_s_1957_: *mut crate::leanh::LeanObject,
    mut v_it_1958_: *mut crate::leanh::LeanObject,
    mut v_acc_1959_: *mut crate::leanh::LeanObject,
    mut v_hP_1960_: *mut crate::leanh::LeanObject,
    mut v_recur_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: u8 = 0;
    v___x_1962_ = lean_nat_dec_eq(v_it_1958_, v___x_1956_);
    if v___x_1962_ == 0 {
        let mut v___x_1963_: u32 = 0;
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1963_ = lean_string_utf8_get_fast(v_s_1957_, v_it_1958_);
        v___x_1964_ = lean_string_utf8_next_fast(v_s_1957_, v_it_1958_);
        v___x_1965_ =
            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_1959_, v___x_1963_);
        v___x_1966_ = crate::leanh::lean_apply_4(
            v_recur_1961_,
            v___x_1964_,
            v___x_1965_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1966_;
    } else {
        crate::leanh::lean_dec_ref(v_recur_1961_);
        return v_acc_1959_;
    }
}
pub unsafe fn l_Lean_Json_escape___lam__0___boxed(
    mut v___x_1967_: *mut crate::leanh::LeanObject,
    mut v_s_1968_: *mut crate::leanh::LeanObject,
    mut v_it_1969_: *mut crate::leanh::LeanObject,
    mut v_acc_1970_: *mut crate::leanh::LeanObject,
    mut v_hP_1971_: *mut crate::leanh::LeanObject,
    mut v_recur_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_Lean_Json_escape___lam__0(
        v___x_1967_,
        v_s_1968_,
        v_it_1969_,
        v_acc_1970_,
        v_hP_1971_,
        v_recur_1972_,
    );
    crate::leanh::lean_dec(v_it_1969_);
    crate::leanh::lean_dec_ref(v_s_1968_);
    crate::leanh::lean_dec(v___x_1967_);
    return v_res_1973_;
}
pub unsafe fn l_Lean_Json_escape(
    mut v_s_1974_: *mut crate::leanh::LeanObject,
    mut v_acc_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1976_: u8 = 0;
    v___x_1976_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1974_);
    if v___x_1976_ == 0 {
        let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1977_ = lean_string_append(v_acc_1975_, v_s_1974_);
        crate::leanh::lean_dec_ref(v_s_1974_);
        return v___x_1977_;
    } else {
        let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1978_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1979_ = lean_string_utf8_byte_size(v_s_1974_);
        crate::leanh::lean_inc_ref(v_s_1974_);
        v___f_1980_ = crate::leanh::lean_alloc_closure(
            l_Lean_Json_escape___lam__0___boxed as *mut core::ffi::c_void,
            6,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1980_, 0, v___x_1979_);
        crate::leanh::lean_closure_set(v___f_1980_, 1, v_s_1974_);
        v___x_1981_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1981_, 0, v_s_1974_);
        crate::leanh::lean_ctor_set(v___x_1981_, 1, v___x_1978_);
        crate::leanh::lean_ctor_set(v___x_1981_, 2, v___x_1979_);
        v___x_1982_ = l_String_Slice_positions(v___x_1981_);
        crate::leanh::lean_dec_ref_known(v___x_1981_, 3);
        v___x_1983_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_1980_,
            v___x_1982_,
            v_acc_1975_,
            crate::leanh::lean_box(0),
        );
        return v___x_1983_;
    }
}
pub unsafe fn l_Lean_Json_renderString(
    mut v_s_1985_: *mut crate::leanh::LeanObject,
    mut v_acc_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    v___x_1987_ = l_Lean_Json_renderString___closed__0;
    v_acc_1988_ = lean_string_append(v_acc_1986_, v___x_1987_);
    v___x_1989_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_1985_);
    if v___x_1989_ == 0 {
        let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1990_ = lean_string_append(v_acc_1988_, v_s_1985_);
        crate::leanh::lean_dec_ref(v_s_1985_);
        v___x_1991_ = lean_string_append(v___x_1990_, v___x_1987_);
        return v___x_1991_;
    } else {
        let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1992_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1993_ = lean_string_utf8_byte_size(v_s_1985_);
        crate::leanh::lean_inc_ref(v_s_1985_);
        v___f_1994_ = crate::leanh::lean_alloc_closure(
            l_Lean_Json_escape___lam__0___boxed as *mut core::ffi::c_void,
            6,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1994_, 0, v___x_1993_);
        crate::leanh::lean_closure_set(v___f_1994_, 1, v_s_1985_);
        v___x_1995_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1995_, 0, v_s_1985_);
        crate::leanh::lean_ctor_set(v___x_1995_, 1, v___x_1992_);
        crate::leanh::lean_ctor_set(v___x_1995_, 2, v___x_1993_);
        v___x_1996_ = l_String_Slice_positions(v___x_1995_);
        crate::leanh::lean_dec_ref_known(v___x_1995_, 3);
        v___x_1997_ = l_WellFounded_opaqueFix_u2083___redArg(
            v___f_1994_,
            v___x_1996_,
            v_acc_1988_,
            crate::leanh::lean_box(0),
        );
        v___x_1998_ = lean_string_append(v___x_1997_, v___x_1987_);
        return v___x_1998_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Json_render_spec__3(
    mut v_a_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = lean_nat_to_int(v_a_1999_);
    return v___x_2000_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(
    mut v___x_2001_: *mut crate::leanh::LeanObject,
    mut v_k_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_b_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: u32 = 0;
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2005_ = crate::leanh::lean_ctor_get(v___x_2001_, 1);
                v_endExclusive_2006_ = crate::leanh::lean_ctor_get(v___x_2001_, 2);
                v___x_2007_ = lean_nat_sub(v_endExclusive_2006_, v_startInclusive_2005_);
                v___x_2008_ = lean_nat_dec_eq(v_a_2003_, v___x_2007_);
                crate::leanh::lean_dec(v___x_2007_);
                if v___x_2008_ == 0 {
                    v___x_2009_ = lean_string_utf8_get_fast(v_k_2002_, v_a_2003_);
                    v___x_2010_ = lean_string_utf8_next_fast(v_k_2002_, v_a_2003_);
                    crate::leanh::lean_dec(v_a_2003_);
                    v___x_2011_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(
                        v_b_2004_,
                        v___x_2009_,
                    );
                    v_a_2003_ = v___x_2010_;
                    v_b_2004_ = v___x_2011_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2003_);
                    return v_b_2004_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg___boxed(
    mut v___x_2013_: *mut crate::leanh::LeanObject,
    mut v_k_2014_: *mut crate::leanh::LeanObject,
    mut v_a_2015_: *mut crate::leanh::LeanObject,
    mut v_b_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(
        v___x_2013_,
        v_k_2014_,
        v_a_2015_,
        v_b_2016_,
    );
    crate::leanh::lean_dec_ref(v_k_2014_);
    crate::leanh::lean_dec_ref(v___x_2013_);
    return v_res_2017_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(
    mut v_x_2018_: *mut crate::leanh::LeanObject,
    mut v_x_2019_: *mut crate::leanh::LeanObject,
    mut v_x_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2020_) == 0 {
                    crate::leanh::lean_dec(v_x_2018_);
                    return v_x_2019_;
                } else {
                    v_head_2021_ = crate::leanh::lean_ctor_get(v_x_2020_, 0);
                    v_tail_2022_ = crate::leanh::lean_ctor_get(v_x_2020_, 1);
                    v_isSharedCheck_2031_ = (!crate::leanh::lean_is_exclusive(v_x_2020_)) as u8;
                    if v_isSharedCheck_2031_ == 0 {
                        v___x_2024_ = v_x_2020_;
                        v_isShared_2025_ = v_isSharedCheck_2031_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2022_);
                        crate::leanh::lean_inc(v_head_2021_);
                        crate::leanh::lean_dec(v_x_2020_);
                        v___x_2024_ = crate::leanh::lean_box(0);
                        v_isShared_2025_ = v_isSharedCheck_2031_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2018_);
                if v_isShared_2025_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2024_, 5);
                    crate::leanh::lean_ctor_set(v___x_2024_, 1, v_x_2018_);
                    crate::leanh::lean_ctor_set(v___x_2024_, 0, v_x_2019_);
                    v___x_2027_ = v___x_2024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2030_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_x_2019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_x_2018_);
                    v___x_2027_ = v_reuseFailAlloc_2030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2028_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2028_, 0, v___x_2027_);
                crate::leanh::lean_ctor_set(v___x_2028_, 1, v_head_2021_);
                v_x_2019_ = v___x_2028_;
                v_x_2020_ = v_tail_2022_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(
    mut v_x_2032_: *mut crate::leanh::LeanObject,
    mut v_x_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2032_) == 0 {
        let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2033_);
        v___x_2034_ = crate::leanh::lean_box(0);
        return v___x_2034_;
    } else {
        let mut v_tail_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2035_ = crate::leanh::lean_ctor_get(v_x_2032_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2035_) == 0 {
            let mut v_head_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2033_);
            v_head_2036_ = crate::leanh::lean_ctor_get(v_x_2032_, 0);
            crate::leanh::lean_inc(v_head_2036_);
            crate::leanh::lean_dec_ref_known(v_x_2032_, 2);
            return v_head_2036_;
        } else {
            let mut v_head_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2035_);
            v_head_2037_ = crate::leanh::lean_ctor_get(v_x_2032_, 0);
            crate::leanh::lean_inc(v_head_2037_);
            crate::leanh::lean_dec_ref_known(v_x_2032_, 2);
            v___x_2038_ =
                l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Json_render_spec__2_spec__2(
                    v_x_2033_,
                    v_head_2037_,
                    v_tail_2035_,
                );
            return v___x_2038_;
        }
    }
}
pub unsafe fn _init_l_Lean_Json_render___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = l_Lean_Json_render___closed__9;
    v___x_2056_ = lean_string_length(v___x_2055_);
    return v___x_2056_;
}
pub unsafe fn _init_l_Lean_Json_render___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__11_once),
        _init_l_Lean_Json_render___closed__11,
    );
    v___x_2058_ = lean_nat_to_int(v___x_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(
    mut v_init_2067_: *mut crate::leanh::LeanObject,
    mut v_x_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2068_) == 0 {
                    v_k_2069_ = crate::leanh::lean_ctor_get(v_x_2068_, 1);
                    crate::leanh::lean_inc(v_k_2069_);
                    v_v_2070_ = crate::leanh::lean_ctor_get(v_x_2068_, 2);
                    crate::leanh::lean_inc(v_v_2070_);
                    v_l_2071_ = crate::leanh::lean_ctor_get(v_x_2068_, 3);
                    crate::leanh::lean_inc(v_l_2071_);
                    v_r_2072_ = crate::leanh::lean_ctor_get(v_x_2068_, 4);
                    crate::leanh::lean_inc(v_r_2072_);
                    crate::leanh::lean_dec_ref_known(v_x_2068_, 5);
                    v___x_2073_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_2067_, v_l_2071_);
                    v___x_2087_ = l_Lean_Json_renderString___closed__0;
                    v___x_2088_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_k_2069_);
                    if v___x_2088_ == 0 {
                        v___x_2089_ = lean_string_append(v___x_2087_, v_k_2069_);
                        crate::leanh::lean_dec(v_k_2069_);
                        v___x_2090_ = lean_string_append(v___x_2089_, v___x_2087_);
                        v___y_2075_ = v___x_2090_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2091_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2092_ = lean_string_utf8_byte_size(v_k_2069_);
                        crate::leanh::lean_inc(v_k_2069_);
                        v___x_2093_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2093_, 0, v_k_2069_);
                        crate::leanh::lean_ctor_set(v___x_2093_, 1, v___x_2091_);
                        crate::leanh::lean_ctor_set(v___x_2093_, 2, v___x_2092_);
                        v___x_2094_ = l_String_Slice_positions(v___x_2093_);
                        v___x_2095_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_2093_, v_k_2069_, v___x_2094_, v___x_2087_);
                        crate::leanh::lean_dec(v_k_2069_);
                        crate::leanh::lean_dec_ref_known(v___x_2093_, 3);
                        v___x_2096_ = lean_string_append(v___x_2095_, v___x_2087_);
                        v___y_2075_ = v___x_2096_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_init_2067_;
                }
            }
            1 => {
                v___x_2076_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2076_, 0, v___y_2075_);
                v___x_2077_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__1;
                v___x_2078_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2078_, 0, v___x_2076_);
                crate::leanh::lean_ctor_set(v___x_2078_, 1, v___x_2077_);
                v___x_2079_ = crate::leanh::lean_box(1);
                v___x_2080_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2080_, 0, v___x_2078_);
                crate::leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
                v___x_2081_ = l_Lean_Json_render(v_v_2070_);
                v___x_2082_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2082_, 0, v___x_2080_);
                crate::leanh::lean_ctor_set(v___x_2082_, 1, v___x_2081_);
                v___x_2083_ = 0;
                v___x_2084_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2082_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2084_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2083_,
                );
                v___x_2085_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2084_);
                crate::leanh::lean_ctor_set(v___x_2085_, 1, v___x_2073_);
                v_init_2067_ = v___x_2085_;
                v_x_2068_ = v_r_2072_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Json_render___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = l_Lean_Json_render___closed__15;
    v___x_2099_ = lean_string_length(v___x_2098_);
    return v___x_2099_;
}
pub unsafe fn _init_l_Lean_Json_render___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2100_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__17_once),
        _init_l_Lean_Json_render___closed__17,
    );
    v___x_2101_ = lean_nat_to_int(v___x_2100_);
    return v___x_2101_;
}
pub unsafe fn l_Lean_Json_render(
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2109_: u8 = 0;
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut v_s_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut v_elems_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2143_: usize = 0;
    let mut v___x_2144_: usize = 0;
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elems_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvs_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2107_) {
                0 => {
                    v___x_2108_ = l_Lean_Json_render___closed__1;
                    return v___x_2108_;
                }
                1 => {
                    v_b_2109_ = crate::leanh::lean_ctor_get_uint8(v_x_2107_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_x_2107_, 0);
                    if v_b_2109_ == 0 {
                        v___x_2110_ = l_Lean_Json_render___closed__3;
                        return v___x_2110_;
                    } else {
                        v___x_2111_ = l_Lean_Json_render___closed__5;
                        return v___x_2111_;
                    }
                }
                2 => {
                    v_n_2112_ = crate::leanh::lean_ctor_get(v_x_2107_, 0);
                    v_isSharedCheck_2120_ = (!crate::leanh::lean_is_exclusive(v_x_2107_)) as u8;
                    if v_isSharedCheck_2120_ == 0 {
                        v___x_2114_ = v_x_2107_;
                        v_isShared_2115_ = v_isSharedCheck_2120_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_2112_);
                        crate::leanh::lean_dec(v_x_2107_);
                        v___x_2114_ = crate::leanh::lean_box(0);
                        v_isShared_2115_ = v_isSharedCheck_2120_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_s_2121_ = crate::leanh::lean_ctor_get(v_x_2107_, 0);
                    v_isSharedCheck_2141_ = (!crate::leanh::lean_is_exclusive(v_x_2107_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v___x_2123_ = v_x_2107_;
                        v_isShared_2124_ = v_isSharedCheck_2141_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_2121_);
                        crate::leanh::lean_dec(v_x_2107_);
                        v___x_2123_ = crate::leanh::lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2141_;
                        state = 3;
                        continue;
                    }
                }
                4 => {
                    v_elems_2142_ = crate::leanh::lean_ctor_get(v_x_2107_, 0);
                    crate::leanh::lean_inc_ref(v_elems_2142_);
                    crate::leanh::lean_dec_ref_known(v_x_2107_, 1);
                    v_sz_2143_ = lean_array_size(v_elems_2142_);
                    v___x_2144_ = 0usize;
                    v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(v_sz_2143_, v___x_2144_, v_elems_2142_);
                    v___x_2146_ = lean_array_to_list(v___x_2145_);
                    v___x_2147_ = l_Lean_Json_render___closed__8;
                    v_elems_2148_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(
                        v___x_2146_,
                        v___x_2147_,
                    );
                    v___x_2149_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__12_once),
                        _init_l_Lean_Json_render___closed__12,
                    );
                    v___x_2150_ = l_Lean_Json_render___closed__13;
                    v___x_2151_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2150_);
                    crate::leanh::lean_ctor_set(v___x_2151_, 1, v_elems_2148_);
                    v___x_2152_ = l_Lean_Json_render___closed__14;
                    v___x_2153_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2153_, 0, v___x_2151_);
                    crate::leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                    v___x_2154_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2149_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 1, v___x_2153_);
                    v___x_2155_ = 0;
                    v___x_2156_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2156_, 0, v___x_2154_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2156_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2155_,
                    );
                    return v___x_2156_;
                }
                _ => {
                    v_kvPairs_2157_ = crate::leanh::lean_ctor_get(v_x_2107_, 0);
                    crate::leanh::lean_inc(v_kvPairs_2157_);
                    crate::leanh::lean_dec_ref_known(v_x_2107_, 1);
                    v___x_2158_ = crate::leanh::lean_box(0);
                    v___x_2159_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v___x_2158_, v_kvPairs_2157_);
                    v___x_2160_ = l_Lean_Json_render___closed__8;
                    v_kvs_2161_ = l_Std_Format_joinSep___at___00Lean_Json_render_spec__2(
                        v___x_2159_,
                        v___x_2160_,
                    );
                    v___x_2162_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__18),
                        core::ptr::addr_of_mut!(l_Lean_Json_render___closed__18_once),
                        _init_l_Lean_Json_render___closed__18,
                    );
                    v___x_2163_ = l_Lean_Json_render___closed__19;
                    v___x_2164_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2163_);
                    crate::leanh::lean_ctor_set(v___x_2164_, 1, v_kvs_2161_);
                    v___x_2165_ = l_Lean_Json_render___closed__20;
                    v___x_2166_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2164_);
                    crate::leanh::lean_ctor_set(v___x_2166_, 1, v___x_2165_);
                    v___x_2167_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2167_, 0, v___x_2162_);
                    crate::leanh::lean_ctor_set(v___x_2167_, 1, v___x_2166_);
                    v___x_2168_ = 0;
                    v___x_2169_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2167_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2169_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2168_,
                    );
                    return v___x_2169_;
                }
            },
            1 => {
                v___x_2116_ = l_Lean_JsonNumber_toString(v_n_2112_);
                if v_isShared_2115_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2114_, 3);
                    crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2116_);
                    v___x_2118_ = v___x_2114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
                    v___x_2118_ = v_reuseFailAlloc_2119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2118_;
            }
            3 => {
                v___x_2125_ = l_Lean_Json_renderString___closed__0;
                v___x_2126_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_s_2121_);
                if v___x_2126_ == 0 {
                    v___x_2127_ = lean_string_append(v___x_2125_, v_s_2121_);
                    crate::leanh::lean_dec_ref(v_s_2121_);
                    v___x_2128_ = lean_string_append(v___x_2127_, v___x_2125_);
                    if v_isShared_2124_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2123_, 0, v___x_2128_);
                        v___x_2130_ = v___x_2123_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2131_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
                        v___x_2130_ = v_reuseFailAlloc_2131_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2132_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2133_ = lean_string_utf8_byte_size(v_s_2121_);
                    crate::leanh::lean_inc_ref(v_s_2121_);
                    v___x_2134_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2134_, 0, v_s_2121_);
                    crate::leanh::lean_ctor_set(v___x_2134_, 1, v___x_2132_);
                    crate::leanh::lean_ctor_set(v___x_2134_, 2, v___x_2133_);
                    v___x_2135_ = l_String_Slice_positions(v___x_2134_);
                    v___x_2136_ =
                        l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(
                            v___x_2134_,
                            v_s_2121_,
                            v___x_2135_,
                            v___x_2125_,
                        );
                    crate::leanh::lean_dec_ref(v_s_2121_);
                    crate::leanh::lean_dec_ref_known(v___x_2134_, 3);
                    v___x_2137_ = lean_string_append(v___x_2136_, v___x_2125_);
                    if v_isShared_2124_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2123_, 0, v___x_2137_);
                        v___x_2139_ = v___x_2123_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2140_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
                        v___x_2139_ = v_reuseFailAlloc_2140_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2130_;
            }
            5 => {
                return v___x_2139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(
    mut v_sz_2170_: usize,
    mut v_i_2171_: usize,
    mut v_bs_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2173_: u8 = 0;
    let mut v_v_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: usize = 0;
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2173_ = lean_usize_dec_lt(v_i_2171_, v_sz_2170_);
                if v___x_2173_ == 0 {
                    return v_bs_2172_;
                } else {
                    v_v_2174_ = lean_array_uget(v_bs_2172_, v_i_2171_);
                    v___x_2175_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2176_ = lean_array_uset(v_bs_2172_, v_i_2171_, v___x_2175_);
                    v___x_2177_ = l_Lean_Json_render(v_v_2174_);
                    v___x_2178_ = 1usize;
                    v___x_2179_ = lean_usize_add(v_i_2171_, v___x_2178_);
                    v___x_2180_ = lean_array_uset(v_bs_x27_2176_, v_i_2171_, v___x_2177_);
                    v_i_2171_ = v___x_2179_;
                    v_bs_2172_ = v___x_2180_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1___boxed(
    mut v_sz_2182_: *mut crate::leanh::LeanObject,
    mut v_i_2183_: *mut crate::leanh::LeanObject,
    mut v_bs_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2185_: usize = 0;
    let mut v_i_boxed_2186_: usize = 0;
    let mut v_res_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2185_ = crate::leanh::lean_unbox_usize(v_sz_2182_);
    crate::leanh::lean_dec(v_sz_2182_);
    v_i_boxed_2186_ = crate::leanh::lean_unbox_usize(v_i_2183_);
    crate::leanh::lean_dec(v_i_2183_);
    v_res_2187_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_render_spec__1(
            v_sz_boxed_2185_,
            v_i_boxed_2186_,
            v_bs_2184_,
        );
    return v_res_2187_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(
    mut v___x_2188_: *mut crate::leanh::LeanObject,
    mut v_k_2189_: *mut crate::leanh::LeanObject,
    mut v_inst_2190_: *mut crate::leanh::LeanObject,
    mut v_R_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
    mut v_b_2193_: *mut crate::leanh::LeanObject,
    mut v_c_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(
        v___x_2188_,
        v_k_2189_,
        v_a_2192_,
        v_b_2193_,
    );
    return v___x_2195_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___boxed(
    mut v___x_2196_: *mut crate::leanh::LeanObject,
    mut v_k_2197_: *mut crate::leanh::LeanObject,
    mut v_inst_2198_: *mut crate::leanh::LeanObject,
    mut v_R_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_b_2201_: *mut crate::leanh::LeanObject,
    mut v_c_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0(
        v___x_2196_,
        v_k_2197_,
        v_inst_2198_,
        v_R_2199_,
        v_a_2200_,
        v_b_2201_,
        v_c_2202_,
    );
    crate::leanh::lean_dec_ref(v_k_2197_);
    crate::leanh::lean_dec_ref(v___x_2196_);
    return v_res_2203_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4(
    mut v_init_2204_: *mut crate::leanh::LeanObject,
    mut v_t_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5(v_init_2204_, v_t_2205_);
    return v___x_2206_;
}
pub unsafe fn l_Lean_Json_pretty(
    mut v_j_2207_: *mut crate::leanh::LeanObject,
    mut v_lineWidth_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = l_Lean_Json_render(v_j_2207_);
    v___x_2210_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2211_ = l_Std_Format_pretty(v___x_2209_, v_lineWidth_2208_, v___x_2210_, v___x_2210_);
    return v___x_2211_;
}
pub unsafe fn l_Lean_Json_pretty___boxed(
    mut v_j_2212_: *mut crate::leanh::LeanObject,
    mut v_lineWidth_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_Json_pretty(v_j_2212_, v_lineWidth_2213_);
    crate::leanh::lean_dec(v_lineWidth_2213_);
    return v_res_2214_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(
    mut v_x_2215_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2215_ {
        0 => {
            let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2216_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2216_;
        }
        1 => {
            let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2217_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2217_;
        }
        2 => {
            let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2218_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2218_;
        }
        3 => {
            let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2219_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2219_;
        }
        4 => {
            let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2220_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2220_;
        }
        _ => {
            let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2221_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2221_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx___boxed(
    mut v_x_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2223_: u8 = 0;
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2223_ = (crate::leanh::lean_unbox(v_x_2222_) as u8);
    v_res_2224_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(
        v_x_boxed_2223_,
    );
    return v_res_2224_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx(
    mut v_x_2225_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2226_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorIdx(v_x_2225_);
    return v___x_2226_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx___boxed(
    mut v_x_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2228_: u8 = 0;
    let mut v_res_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2228_ = (crate::leanh::lean_unbox(v_x_2227_) as u8);
    v_res_2229_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_toCtorIdx(
        v_x_4__boxed_2228_,
    );
    return v_res_2229_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(
    mut v_k_2230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2230_);
    return v_k_2230_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg___boxed(
    mut v_k_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2232_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___redArg(
            v_k_2231_,
        );
    crate::leanh::lean_dec(v_k_2231_);
    return v_res_2232_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(
    mut v_motive_2233_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2234_: *mut crate::leanh::LeanObject,
    mut v_t_2235_: u8,
    mut v_h_2236_: *mut crate::leanh::LeanObject,
    mut v_k_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2237_);
    return v_k_2237_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim___boxed(
    mut v_motive_2238_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2239_: *mut crate::leanh::LeanObject,
    mut v_t_2240_: *mut crate::leanh::LeanObject,
    mut v_h_2241_: *mut crate::leanh::LeanObject,
    mut v_k_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2243_: u8 = 0;
    let mut v_res_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2243_ = (crate::leanh::lean_unbox(v_t_2240_) as u8);
    v_res_2244_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_ctorElim(
        v_motive_2238_,
        v_ctorIdx_2239_,
        v_t_boxed_2243_,
        v_h_2241_,
        v_k_2242_,
    );
    crate::leanh::lean_dec(v_k_2242_);
    crate::leanh::lean_dec(v_ctorIdx_2239_);
    return v_res_2244_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(
    mut v_json_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_json_2245_);
    return v_json_2245_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg___boxed(
    mut v_json_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___redArg(
            v_json_2246_,
        );
    crate::leanh::lean_dec(v_json_2246_);
    return v_res_2247_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(
    mut v_motive_2248_: *mut crate::leanh::LeanObject,
    mut v_t_2249_: u8,
    mut v_h_2250_: *mut crate::leanh::LeanObject,
    mut v_json_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_json_2251_);
    return v_json_2251_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim___boxed(
    mut v_motive_2252_: *mut crate::leanh::LeanObject,
    mut v_t_2253_: *mut crate::leanh::LeanObject,
    mut v_h_2254_: *mut crate::leanh::LeanObject,
    mut v_json_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2256_: u8 = 0;
    let mut v_res_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2256_ = (crate::leanh::lean_unbox(v_t_2253_) as u8);
    v_res_2257_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_json_elim(
        v_motive_2252_,
        v_t_boxed_2256_,
        v_h_2254_,
        v_json_2255_,
    );
    crate::leanh::lean_dec(v_json_2255_);
    return v_res_2257_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(
    mut v_arrayElem_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_arrayElem_2258_);
    return v_arrayElem_2258_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg___boxed(
    mut v_arrayElem_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___redArg(v_arrayElem_2259_);
    crate::leanh::lean_dec(v_arrayElem_2259_);
    return v_res_2260_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(
    mut v_motive_2261_: *mut crate::leanh::LeanObject,
    mut v_t_2262_: u8,
    mut v_h_2263_: *mut crate::leanh::LeanObject,
    mut v_arrayElem_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_arrayElem_2264_);
    return v_arrayElem_2264_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim___boxed(
    mut v_motive_2265_: *mut crate::leanh::LeanObject,
    mut v_t_2266_: *mut crate::leanh::LeanObject,
    mut v_h_2267_: *mut crate::leanh::LeanObject,
    mut v_arrayElem_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2269_: u8 = 0;
    let mut v_res_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2269_ = (crate::leanh::lean_unbox(v_t_2266_) as u8);
    v_res_2270_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayElem_elim(
            v_motive_2265_,
            v_t_boxed_2269_,
            v_h_2267_,
            v_arrayElem_2268_,
        );
    crate::leanh::lean_dec(v_arrayElem_2268_);
    return v_res_2270_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(
    mut v_arrayEnd_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_arrayEnd_2271_);
    return v_arrayEnd_2271_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg___boxed(
    mut v_arrayEnd_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2273_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___redArg(
            v_arrayEnd_2272_,
        );
    crate::leanh::lean_dec(v_arrayEnd_2272_);
    return v_res_2273_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(
    mut v_motive_2274_: *mut crate::leanh::LeanObject,
    mut v_t_2275_: u8,
    mut v_h_2276_: *mut crate::leanh::LeanObject,
    mut v_arrayEnd_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_arrayEnd_2277_);
    return v_arrayEnd_2277_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim___boxed(
    mut v_motive_2278_: *mut crate::leanh::LeanObject,
    mut v_t_2279_: *mut crate::leanh::LeanObject,
    mut v_h_2280_: *mut crate::leanh::LeanObject,
    mut v_arrayEnd_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2282_: u8 = 0;
    let mut v_res_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2282_ = (crate::leanh::lean_unbox(v_t_2279_) as u8);
    v_res_2283_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_arrayEnd_elim(
            v_motive_2278_,
            v_t_boxed_2282_,
            v_h_2280_,
            v_arrayEnd_2281_,
        );
    crate::leanh::lean_dec(v_arrayEnd_2281_);
    return v_res_2283_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(
    mut v_objectField_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_objectField_2284_);
    return v_objectField_2284_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg___boxed(
    mut v_objectField_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___redArg(v_objectField_2285_);
    crate::leanh::lean_dec(v_objectField_2285_);
    return v_res_2286_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(
    mut v_motive_2287_: *mut crate::leanh::LeanObject,
    mut v_t_2288_: u8,
    mut v_h_2289_: *mut crate::leanh::LeanObject,
    mut v_objectField_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_objectField_2290_);
    return v_objectField_2290_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim___boxed(
    mut v_motive_2291_: *mut crate::leanh::LeanObject,
    mut v_t_2292_: *mut crate::leanh::LeanObject,
    mut v_h_2293_: *mut crate::leanh::LeanObject,
    mut v_objectField_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2295_: u8 = 0;
    let mut v_res_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2295_ = (crate::leanh::lean_unbox(v_t_2292_) as u8);
    v_res_2296_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectField_elim(
            v_motive_2291_,
            v_t_boxed_2295_,
            v_h_2293_,
            v_objectField_2294_,
        );
    crate::leanh::lean_dec(v_objectField_2294_);
    return v_res_2296_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(
    mut v_objectEnd_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_objectEnd_2297_);
    return v_objectEnd_2297_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg___boxed(
    mut v_objectEnd_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2299_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___redArg(v_objectEnd_2298_);
    crate::leanh::lean_dec(v_objectEnd_2298_);
    return v_res_2299_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(
    mut v_motive_2300_: *mut crate::leanh::LeanObject,
    mut v_t_2301_: u8,
    mut v_h_2302_: *mut crate::leanh::LeanObject,
    mut v_objectEnd_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_objectEnd_2303_);
    return v_objectEnd_2303_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim___boxed(
    mut v_motive_2304_: *mut crate::leanh::LeanObject,
    mut v_t_2305_: *mut crate::leanh::LeanObject,
    mut v_h_2306_: *mut crate::leanh::LeanObject,
    mut v_objectEnd_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2308_: u8 = 0;
    let mut v_res_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2308_ = (crate::leanh::lean_unbox(v_t_2305_) as u8);
    v_res_2309_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_objectEnd_elim(
            v_motive_2304_,
            v_t_boxed_2308_,
            v_h_2306_,
            v_objectEnd_2307_,
        );
    crate::leanh::lean_dec(v_objectEnd_2307_);
    return v_res_2309_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(
    mut v_comma_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_comma_2310_);
    return v_comma_2310_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg___boxed(
    mut v_comma_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2312_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___redArg(
            v_comma_2311_,
        );
    crate::leanh::lean_dec(v_comma_2311_);
    return v_res_2312_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(
    mut v_motive_2313_: *mut crate::leanh::LeanObject,
    mut v_t_2314_: u8,
    mut v_h_2315_: *mut crate::leanh::LeanObject,
    mut v_comma_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_comma_2316_);
    return v_comma_2316_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim___boxed(
    mut v_motive_2317_: *mut crate::leanh::LeanObject,
    mut v_t_2318_: *mut crate::leanh::LeanObject,
    mut v_h_2319_: *mut crate::leanh::LeanObject,
    mut v_comma_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2321_: u8 = 0;
    let mut v_res_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2321_ = (crate::leanh::lean_unbox(v_t_2318_) as u8);
    v_res_2322_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemKind_comma_elim(
        v_motive_2317_,
        v_t_boxed_2321_,
        v_h_2319_,
        v_comma_2320_,
    );
    crate::leanh::lean_dec(v_comma_2320_);
    return v_res_2322_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(
    mut v_q_2323_: *mut crate::leanh::LeanObject,
    mut v_kind_2324_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2325_ = crate::leanh::lean_ctor_get(v_q_2323_, 0);
                v_values_2326_ = crate::leanh::lean_ctor_get(v_q_2323_, 1);
                v_objectFieldKeys_2327_ = crate::leanh::lean_ctor_get(v_q_2323_, 2);
                v_isSharedCheck_2336_ = (!crate::leanh::lean_is_exclusive(v_q_2323_)) as u8;
                if v_isSharedCheck_2336_ == 0 {
                    v___x_2329_ = v_q_2323_;
                    v_isShared_2330_ = v_isSharedCheck_2336_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2327_);
                    crate::leanh::lean_inc(v_values_2326_);
                    crate::leanh::lean_inc(v_kinds_2325_);
                    crate::leanh::lean_dec(v_q_2323_);
                    v___x_2329_ = crate::leanh::lean_box(0);
                    v_isShared_2330_ = v_isSharedCheck_2336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2331_ = crate::leanh::lean_box((v_kind_2324_) as usize);
                v___x_2332_ = lean_array_push(v_kinds_2325_, v___x_2331_);
                if v_isShared_2330_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2329_, 0, v___x_2332_);
                    v___x_2334_ = v___x_2329_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2335_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_values_2326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_objectFieldKeys_2327_);
                    v___x_2334_ = v_reuseFailAlloc_2335_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind___boxed(
    mut v_q_2337_: *mut crate::leanh::LeanObject,
    mut v_kind_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2339_: u8 = 0;
    let mut v_res_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2339_ = (crate::leanh::lean_unbox(v_kind_2338_) as u8);
    v_res_2340_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushKind(
        v_q_2337_,
        v_kind_boxed_2339_,
    );
    return v_res_2340_;
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushValue(
    mut v_q_2341_: *mut crate::leanh::LeanObject,
    mut v_value_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2343_ = crate::leanh::lean_ctor_get(v_q_2341_, 0);
                v_values_2344_ = crate::leanh::lean_ctor_get(v_q_2341_, 1);
                v_objectFieldKeys_2345_ = crate::leanh::lean_ctor_get(v_q_2341_, 2);
                v_isSharedCheck_2353_ = (!crate::leanh::lean_is_exclusive(v_q_2341_)) as u8;
                if v_isSharedCheck_2353_ == 0 {
                    v___x_2347_ = v_q_2341_;
                    v_isShared_2348_ = v_isSharedCheck_2353_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2345_);
                    crate::leanh::lean_inc(v_values_2344_);
                    crate::leanh::lean_inc(v_kinds_2343_);
                    crate::leanh::lean_dec(v_q_2341_);
                    v___x_2347_ = crate::leanh::lean_box(0);
                    v_isShared_2348_ = v_isSharedCheck_2353_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2349_ = lean_array_push(v_values_2344_, v_value_2342_);
                if v_isShared_2348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2347_, 1, v___x_2349_);
                    v___x_2351_ = v___x_2347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2352_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_kinds_2343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_objectFieldKeys_2345_);
                    v___x_2351_ = v_reuseFailAlloc_2352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_pushObjectFieldKey(
    mut v_q_2354_: *mut crate::leanh::LeanObject,
    mut v_objectFieldKey_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2356_ = crate::leanh::lean_ctor_get(v_q_2354_, 0);
                v_values_2357_ = crate::leanh::lean_ctor_get(v_q_2354_, 1);
                v_objectFieldKeys_2358_ = crate::leanh::lean_ctor_get(v_q_2354_, 2);
                v_isSharedCheck_2366_ = (!crate::leanh::lean_is_exclusive(v_q_2354_)) as u8;
                if v_isSharedCheck_2366_ == 0 {
                    v___x_2360_ = v_q_2354_;
                    v_isShared_2361_ = v_isSharedCheck_2366_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2358_);
                    crate::leanh::lean_inc(v_values_2357_);
                    crate::leanh::lean_inc(v_kinds_2356_);
                    crate::leanh::lean_dec(v_q_2354_);
                    v___x_2360_ = crate::leanh::lean_box(0);
                    v_isShared_2361_ = v_isSharedCheck_2366_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2362_ = lean_array_push(v_objectFieldKeys_2358_, v_objectFieldKey_2355_);
                if v_isShared_2361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2360_, 2, v___x_2362_);
                    v___x_2364_ = v___x_2360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_kinds_2356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_values_2357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 2, v___x_2362_);
                    v___x_2364_ = v_reuseFailAlloc_2365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind___redArg(
    mut v_q_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2368_ = crate::leanh::lean_ctor_get(v_q_2367_, 0);
                v_values_2369_ = crate::leanh::lean_ctor_get(v_q_2367_, 1);
                v_objectFieldKeys_2370_ = crate::leanh::lean_ctor_get(v_q_2367_, 2);
                v_isSharedCheck_2383_ = (!crate::leanh::lean_is_exclusive(v_q_2367_)) as u8;
                if v_isSharedCheck_2383_ == 0 {
                    v___x_2372_ = v_q_2367_;
                    v_isShared_2373_ = v_isSharedCheck_2383_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2370_);
                    crate::leanh::lean_inc(v_values_2369_);
                    crate::leanh::lean_inc(v_kinds_2368_);
                    crate::leanh::lean_dec(v_q_2367_);
                    v___x_2372_ = crate::leanh::lean_box(0);
                    v_isShared_2373_ = v_isSharedCheck_2383_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2374_ = lean_array_get_size(v_kinds_2368_);
                v___x_2375_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2376_ = lean_nat_sub(v___x_2374_, v___x_2375_);
                v_kind_2377_ = lean_array_fget(v_kinds_2368_, v___x_2376_);
                crate::leanh::lean_dec(v___x_2376_);
                v___x_2378_ = lean_array_pop(v_kinds_2368_);
                if v_isShared_2373_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2372_, 0, v___x_2378_);
                    v_q_2380_ = v___x_2372_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2382_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_values_2369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_objectFieldKeys_2370_);
                    v_q_2380_ = v_reuseFailAlloc_2382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2381_, 0, v_kind_2377_);
                crate::leanh::lean_ctor_set(v___x_2381_, 1, v_q_2380_);
                return v___x_2381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popKind(
    mut v_q_2384_: *mut crate::leanh::LeanObject,
    mut v_h_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2386_ = crate::leanh::lean_ctor_get(v_q_2384_, 0);
                v_values_2387_ = crate::leanh::lean_ctor_get(v_q_2384_, 1);
                v_objectFieldKeys_2388_ = crate::leanh::lean_ctor_get(v_q_2384_, 2);
                v_isSharedCheck_2401_ = (!crate::leanh::lean_is_exclusive(v_q_2384_)) as u8;
                if v_isSharedCheck_2401_ == 0 {
                    v___x_2390_ = v_q_2384_;
                    v_isShared_2391_ = v_isSharedCheck_2401_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2388_);
                    crate::leanh::lean_inc(v_values_2387_);
                    crate::leanh::lean_inc(v_kinds_2386_);
                    crate::leanh::lean_dec(v_q_2384_);
                    v___x_2390_ = crate::leanh::lean_box(0);
                    v_isShared_2391_ = v_isSharedCheck_2401_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2392_ = lean_array_get_size(v_kinds_2386_);
                v___x_2393_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2394_ = lean_nat_sub(v___x_2392_, v___x_2393_);
                v_kind_2395_ = lean_array_fget(v_kinds_2386_, v___x_2394_);
                crate::leanh::lean_dec(v___x_2394_);
                v___x_2396_ = lean_array_pop(v_kinds_2386_);
                if v_isShared_2391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2390_, 0, v___x_2396_);
                    v_q_2398_ = v___x_2390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_values_2387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_objectFieldKeys_2388_);
                    v_q_2398_ = v_reuseFailAlloc_2400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2399_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2399_, 0, v_kind_2395_);
                crate::leanh::lean_ctor_set(v___x_2399_, 1, v_q_2398_);
                return v___x_2399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popValue_x21(
    mut v_q_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2403_ = crate::leanh::lean_ctor_get(v_q_2402_, 0);
                v_values_2404_ = crate::leanh::lean_ctor_get(v_q_2402_, 1);
                v_objectFieldKeys_2405_ = crate::leanh::lean_ctor_get(v_q_2402_, 2);
                v_isSharedCheck_2419_ = (!crate::leanh::lean_is_exclusive(v_q_2402_)) as u8;
                if v_isSharedCheck_2419_ == 0 {
                    v___x_2407_ = v_q_2402_;
                    v_isShared_2408_ = v_isSharedCheck_2419_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2405_);
                    crate::leanh::lean_inc(v_values_2404_);
                    crate::leanh::lean_inc(v_kinds_2403_);
                    crate::leanh::lean_dec(v_q_2402_);
                    v___x_2407_ = crate::leanh::lean_box(0);
                    v_isShared_2408_ = v_isSharedCheck_2419_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2409_ = crate::leanh::lean_box(0);
                v___x_2410_ = lean_array_get_size(v_values_2404_);
                v___x_2411_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2412_ = lean_nat_sub(v___x_2410_, v___x_2411_);
                v_value_2413_ = lean_array_get(v___x_2409_, v_values_2404_, v___x_2412_);
                crate::leanh::lean_dec(v___x_2412_);
                v___x_2414_ = lean_array_pop(v_values_2404_);
                if v_isShared_2408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2407_, 1, v___x_2414_);
                    v_q_2416_ = v___x_2407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_kinds_2403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___x_2414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_objectFieldKeys_2405_);
                    v_q_2416_ = v_reuseFailAlloc_2418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2417_, 0, v_value_2413_);
                crate::leanh::lean_ctor_set(v___x_2417_, 1, v_q_2416_);
                return v___x_2417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21(
    mut v_q_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKey_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2422_ = crate::leanh::lean_ctor_get(v_q_2421_, 0);
                v_values_2423_ = crate::leanh::lean_ctor_get(v_q_2421_, 1);
                v_objectFieldKeys_2424_ = crate::leanh::lean_ctor_get(v_q_2421_, 2);
                v_isSharedCheck_2438_ = (!crate::leanh::lean_is_exclusive(v_q_2421_)) as u8;
                if v_isSharedCheck_2438_ == 0 {
                    v___x_2426_ = v_q_2421_;
                    v_isShared_2427_ = v_isSharedCheck_2438_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2424_);
                    crate::leanh::lean_inc(v_values_2423_);
                    crate::leanh::lean_inc(v_kinds_2422_);
                    crate::leanh::lean_dec(v_q_2421_);
                    v___x_2426_ = crate::leanh::lean_box(0);
                    v_isShared_2427_ = v_isSharedCheck_2438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2428_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0;
                v___x_2429_ = lean_array_get_size(v_objectFieldKeys_2424_);
                v___x_2430_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2431_ = lean_nat_sub(v___x_2429_, v___x_2430_);
                v_objectFieldKey_2432_ =
                    lean_array_get(v___x_2428_, v_objectFieldKeys_2424_, v___x_2431_);
                crate::leanh::lean_dec(v___x_2431_);
                v___x_2433_ = lean_array_pop(v_objectFieldKeys_2424_);
                if v_isShared_2427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2426_, 2, v___x_2433_);
                    v_q_2435_ = v___x_2426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_kinds_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_values_2423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 2, v___x_2433_);
                    v_q_2435_ = v_reuseFailAlloc_2437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2436_, 0, v_objectFieldKey_2432_);
                crate::leanh::lean_ctor_set(v___x_2436_, 1, v_q_2435_);
                return v___x_2436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(
    mut v_as_2439_: *mut crate::leanh::LeanObject,
    mut v_i_2440_: usize,
    mut v_stop_2441_: usize,
    mut v_b_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: u8 = 0;
    let mut v_kinds_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2443_ = lean_usize_dec_eq(v_i_2440_, v_stop_2441_);
                if v___x_2443_ == 0 {
                    v_kinds_2444_ = crate::leanh::lean_ctor_get(v_b_2442_, 0);
                    v_values_2445_ = crate::leanh::lean_ctor_get(v_b_2442_, 1);
                    v_objectFieldKeys_2446_ = crate::leanh::lean_ctor_get(v_b_2442_, 2);
                    v_isSharedCheck_2461_ = (!crate::leanh::lean_is_exclusive(v_b_2442_)) as u8;
                    if v_isSharedCheck_2461_ == 0 {
                        v___x_2448_ = v_b_2442_;
                        v_isShared_2449_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_objectFieldKeys_2446_);
                        crate::leanh::lean_inc(v_values_2445_);
                        crate::leanh::lean_inc(v_kinds_2444_);
                        crate::leanh::lean_dec(v_b_2442_);
                        v___x_2448_ = crate::leanh::lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2461_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2442_;
                }
            }
            1 => {
                v___x_2450_ = 1usize;
                v___x_2451_ = lean_usize_sub(v_i_2440_, v___x_2450_);
                v___x_2452_ = lean_array_uget_borrowed(v_as_2439_, v___x_2451_);
                v___x_2453_ = 1;
                v___x_2454_ = crate::leanh::lean_box((v___x_2453_) as usize);
                v___x_2455_ = lean_array_push(v_kinds_2444_, v___x_2454_);
                crate::leanh::lean_inc(v___x_2452_);
                v___x_2456_ = lean_array_push(v_values_2445_, v___x_2452_);
                if v_isShared_2449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2448_, 1, v___x_2456_);
                    crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2455_);
                    v___x_2458_ = v___x_2448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_objectFieldKeys_2446_);
                    v___x_2458_ = v_reuseFailAlloc_2460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_i_2440_ = v___x_2451_;
                v_b_2442_ = v___x_2458_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0___boxed(
    mut v_as_2462_: *mut crate::leanh::LeanObject,
    mut v_i_2463_: *mut crate::leanh::LeanObject,
    mut v_stop_2464_: *mut crate::leanh::LeanObject,
    mut v_b_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2466_: usize = 0;
    let mut v_stop_boxed_2467_: usize = 0;
    let mut v_res_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2466_ = crate::leanh::lean_unbox_usize(v_i_2463_);
    crate::leanh::lean_dec(v_i_2463_);
    v_stop_boxed_2467_ = crate::leanh::lean_unbox_usize(v_stop_2464_);
    crate::leanh::lean_dec(v_stop_2464_);
    v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_as_2462_, v_i_boxed_2466_, v_stop_boxed_2467_, v_b_2465_);
    crate::leanh::lean_dec_ref(v_as_2462_);
    return v_res_2468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(
    mut v_init_2469_: *mut crate::leanh::LeanObject,
    mut v_x_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kinds_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2481_: u8 = 0;
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2470_) == 0 {
                    v_k_2471_ = crate::leanh::lean_ctor_get(v_x_2470_, 1);
                    crate::leanh::lean_inc(v_k_2471_);
                    v_v_2472_ = crate::leanh::lean_ctor_get(v_x_2470_, 2);
                    crate::leanh::lean_inc(v_v_2472_);
                    v_l_2473_ = crate::leanh::lean_ctor_get(v_x_2470_, 3);
                    crate::leanh::lean_inc(v_l_2473_);
                    v_r_2474_ = crate::leanh::lean_ctor_get(v_x_2470_, 4);
                    crate::leanh::lean_inc(v_r_2474_);
                    crate::leanh::lean_dec_ref_known(v_x_2470_, 5);
                    v___x_2475_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_init_2469_, v_r_2474_);
                    v_kinds_2476_ = crate::leanh::lean_ctor_get(v___x_2475_, 0);
                    v_values_2477_ = crate::leanh::lean_ctor_get(v___x_2475_, 1);
                    v_objectFieldKeys_2478_ = crate::leanh::lean_ctor_get(v___x_2475_, 2);
                    v_isSharedCheck_2491_ = (!crate::leanh::lean_is_exclusive(v___x_2475_)) as u8;
                    if v_isSharedCheck_2491_ == 0 {
                        v___x_2480_ = v___x_2475_;
                        v_isShared_2481_ = v_isSharedCheck_2491_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_objectFieldKeys_2478_);
                        crate::leanh::lean_inc(v_values_2477_);
                        crate::leanh::lean_inc(v_kinds_2476_);
                        crate::leanh::lean_dec(v___x_2475_);
                        v___x_2480_ = crate::leanh::lean_box(0);
                        v_isShared_2481_ = v_isSharedCheck_2491_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_init_2469_;
                }
            }
            1 => {
                v___x_2482_ = 3;
                v___x_2483_ = crate::leanh::lean_box((v___x_2482_) as usize);
                v___x_2484_ = lean_array_push(v_kinds_2476_, v___x_2483_);
                v___x_2485_ = lean_array_push(v_objectFieldKeys_2478_, v_k_2471_);
                v___x_2486_ = lean_array_push(v_values_2477_, v_v_2472_);
                if v_isShared_2481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2480_, 2, v___x_2485_);
                    crate::leanh::lean_ctor_set(v___x_2480_, 1, v___x_2486_);
                    crate::leanh::lean_ctor_set(v___x_2480_, 0, v___x_2484_);
                    v___x_2488_ = v___x_2480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 2, v___x_2485_);
                    v___x_2488_ = v_reuseFailAlloc_2490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_init_2469_ = v___x_2488_;
                v_x_2470_ = v_l_2473_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(
    mut v_acc_2502_: *mut crate::leanh::LeanObject,
    mut v_q_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kinds_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_values_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKeys_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2509_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: u8 = 0;
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: u8 = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2533_: u8 = 0;
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elems_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2563_: usize = 0;
    let mut v___x_2564_: usize = 0;
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_objectFieldKey_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: u8 = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kinds_2504_ = crate::leanh::lean_ctor_get(v_q_2503_, 0);
                v_values_2505_ = crate::leanh::lean_ctor_get(v_q_2503_, 1);
                v_objectFieldKeys_2506_ = crate::leanh::lean_ctor_get(v_q_2503_, 2);
                v_isSharedCheck_2695_ = (!crate::leanh::lean_is_exclusive(v_q_2503_)) as u8;
                if v_isSharedCheck_2695_ == 0 {
                    v___x_2508_ = v_q_2503_;
                    v_isShared_2509_ = v_isSharedCheck_2695_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_objectFieldKeys_2506_);
                    crate::leanh::lean_inc(v_values_2505_);
                    crate::leanh::lean_inc(v_kinds_2504_);
                    crate::leanh::lean_dec(v_q_2503_);
                    v___x_2508_ = crate::leanh::lean_box(0);
                    v_isShared_2509_ = v_isSharedCheck_2695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2510_ = lean_array_get_size(v_kinds_2504_);
                v___x_2511_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2512_ = lean_nat_dec_eq(v___x_2510_, v___x_2511_);
                if v___x_2512_ == 0 {
                    v___x_2513_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2514_ = lean_nat_sub(v___x_2510_, v___x_2513_);
                    v_kind_2515_ = lean_array_fget(v_kinds_2504_, v___x_2514_);
                    crate::leanh::lean_dec(v___x_2514_);
                    v___x_2516_ = lean_array_pop(v_kinds_2504_);
                    crate::leanh::lean_inc_ref(v_objectFieldKeys_2506_);
                    crate::leanh::lean_inc_ref(v_values_2505_);
                    crate::leanh::lean_inc_ref(v___x_2516_);
                    if v_isShared_2509_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2516_);
                        v_q_2518_ = v___x_2508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2694_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2516_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_values_2505_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2694_,
                            2,
                            v_objectFieldKeys_2506_,
                        );
                        v_q_2518_ = v_reuseFailAlloc_2694_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2508_);
                    crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                    crate::leanh::lean_dec_ref(v_values_2505_);
                    crate::leanh::lean_dec_ref(v_kinds_2504_);
                    return v_acc_2502_;
                }
            }
            2 => {
                v___x_2519_ = (crate::leanh::lean_unbox(v_kind_2515_) as u8);
                crate::leanh::lean_dec(v_kind_2515_);
                match v___x_2519_ {
                    0 => {
                        crate::leanh::lean_dec_ref(v_q_2518_);
                        v___x_2520_ = crate::leanh::lean_box(0);
                        v___x_2521_ = lean_array_get_size(v_values_2505_);
                        v___x_2522_ = lean_nat_sub(v___x_2521_, v___x_2513_);
                        v_value_2523_ = lean_array_get(v___x_2520_, v_values_2505_, v___x_2522_);
                        crate::leanh::lean_dec(v___x_2522_);
                        v___x_2524_ = lean_array_pop(v_values_2505_);
                        crate::leanh::lean_inc_ref(v_objectFieldKeys_2506_);
                        crate::leanh::lean_inc_ref(v___x_2524_);
                        crate::leanh::lean_inc_ref(v___x_2516_);
                        v_q_2525_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_q_2525_, 0, v___x_2516_);
                        crate::leanh::lean_ctor_set(v_q_2525_, 1, v___x_2524_);
                        crate::leanh::lean_ctor_set(v_q_2525_, 2, v_objectFieldKeys_2506_);
                        match crate::leanh::lean_obj_tag(v_value_2523_) {
                            0 => {
                                crate::leanh::lean_dec_ref(v___x_2524_);
                                crate::leanh::lean_dec_ref(v___x_2516_);
                                crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                                v___x_2530_ = l_Lean_Json_render___closed__0;
                                v___x_2531_ = lean_string_append(v_acc_2502_, v___x_2530_);
                                v_acc_2502_ = v___x_2531_;
                                v_q_2503_ = v_q_2525_;
                                state = 0;
                                continue;
                            }
                            1 => {
                                crate::leanh::lean_dec_ref(v___x_2524_);
                                crate::leanh::lean_dec_ref(v___x_2516_);
                                crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                                v_b_2533_ =
                                    crate::leanh::lean_ctor_get_uint8(v_value_2523_, 0 as u32);
                                crate::leanh::lean_dec_ref_known(v_value_2523_, 0);
                                if v_b_2533_ == 0 {
                                    v___x_2534_ = l_Lean_Json_render___closed__2;
                                    v___y_2527_ = v___x_2534_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_2535_ = l_Lean_Json_render___closed__4;
                                    v___y_2527_ = v___x_2535_;
                                    state = 3;
                                    continue;
                                }
                            }
                            2 => {
                                crate::leanh::lean_dec_ref(v___x_2524_);
                                crate::leanh::lean_dec_ref(v___x_2516_);
                                crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                                v_n_2536_ = crate::leanh::lean_ctor_get(v_value_2523_, 0);
                                crate::leanh::lean_inc_ref(v_n_2536_);
                                crate::leanh::lean_dec_ref_known(v_value_2523_, 1);
                                v___x_2537_ = l_Lean_JsonNumber_toString(v_n_2536_);
                                v___x_2538_ = lean_string_append(v_acc_2502_, v___x_2537_);
                                crate::leanh::lean_dec_ref(v___x_2537_);
                                v_acc_2502_ = v___x_2538_;
                                v_q_2503_ = v_q_2525_;
                                state = 0;
                                continue;
                            }
                            3 => {
                                crate::leanh::lean_dec_ref(v___x_2524_);
                                crate::leanh::lean_dec_ref(v___x_2516_);
                                crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                                v_s_2540_ = crate::leanh::lean_ctor_get(v_value_2523_, 0);
                                crate::leanh::lean_inc_ref(v_s_2540_);
                                crate::leanh::lean_dec_ref_known(v_value_2523_, 1);
                                v___x_2541_ = l_Lean_Json_renderString___closed__0;
                                v_acc_2542_ = lean_string_append(v_acc_2502_, v___x_2541_);
                                v___x_2543_ =
                                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(
                                        v_s_2540_,
                                    );
                                if v___x_2543_ == 0 {
                                    v___x_2544_ = lean_string_append(v_acc_2542_, v_s_2540_);
                                    crate::leanh::lean_dec_ref(v_s_2540_);
                                    v___x_2545_ = lean_string_append(v___x_2544_, v___x_2541_);
                                    v_acc_2502_ = v___x_2545_;
                                    v_q_2503_ = v_q_2525_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_2547_ = lean_string_utf8_byte_size(v_s_2540_);
                                    crate::leanh::lean_inc_ref(v_s_2540_);
                                    v___x_2548_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2548_, 0, v_s_2540_);
                                    crate::leanh::lean_ctor_set(v___x_2548_, 1, v___x_2511_);
                                    crate::leanh::lean_ctor_set(v___x_2548_, 2, v___x_2547_);
                                    v___x_2549_ = l_String_Slice_positions(v___x_2548_);
                                    v___x_2550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_2548_, v_s_2540_, v___x_2549_, v_acc_2542_);
                                    crate::leanh::lean_dec_ref(v_s_2540_);
                                    crate::leanh::lean_dec_ref_known(v___x_2548_, 3);
                                    v___x_2551_ = lean_string_append(v___x_2550_, v___x_2541_);
                                    v_acc_2502_ = v___x_2551_;
                                    v_q_2503_ = v_q_2525_;
                                    state = 0;
                                    continue;
                                }
                            }
                            4 => {
                                crate::leanh::lean_dec_ref_known(v_q_2525_, 3);
                                v_elems_2553_ = crate::leanh::lean_ctor_get(v_value_2523_, 0);
                                crate::leanh::lean_inc_ref(v_elems_2553_);
                                crate::leanh::lean_dec_ref_known(v_value_2523_, 1);
                                v___x_2554_ = 2;
                                v___x_2555_ = crate::leanh::lean_box((v___x_2554_) as usize);
                                v___x_2556_ = lean_array_push(v___x_2516_, v___x_2555_);
                                v_q_2557_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_q_2557_, 0, v___x_2556_);
                                crate::leanh::lean_ctor_set(v_q_2557_, 1, v___x_2524_);
                                crate::leanh::lean_ctor_set(v_q_2557_, 2, v_objectFieldKeys_2506_);
                                v___x_2558_ = l_Lean_Json_render___closed__9;
                                v___x_2559_ = lean_string_append(v_acc_2502_, v___x_2558_);
                                v___x_2560_ = lean_array_get_size(v_elems_2553_);
                                v___x_2561_ = lean_nat_dec_lt(v___x_2511_, v___x_2560_);
                                if v___x_2561_ == 0 {
                                    crate::leanh::lean_dec_ref(v_elems_2553_);
                                    v_acc_2502_ = v___x_2559_;
                                    v_q_2503_ = v_q_2557_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_2563_ = lean_usize_of_nat(v___x_2560_);
                                    v___x_2564_ = 0usize;
                                    v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__0(v_elems_2553_, v___x_2563_, v___x_2564_, v_q_2557_);
                                    crate::leanh::lean_dec_ref(v_elems_2553_);
                                    v_acc_2502_ = v___x_2559_;
                                    v_q_2503_ = v___x_2565_;
                                    state = 0;
                                    continue;
                                }
                            }
                            _ => {
                                crate::leanh::lean_dec_ref_known(v_q_2525_, 3);
                                v_kvPairs_2567_ = crate::leanh::lean_ctor_get(v_value_2523_, 0);
                                crate::leanh::lean_inc(v_kvPairs_2567_);
                                crate::leanh::lean_dec_ref_known(v_value_2523_, 1);
                                v___x_2568_ = 4;
                                v___x_2569_ = crate::leanh::lean_box((v___x_2568_) as usize);
                                v___x_2570_ = lean_array_push(v___x_2516_, v___x_2569_);
                                v_q_2571_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_q_2571_, 0, v___x_2570_);
                                crate::leanh::lean_ctor_set(v_q_2571_, 1, v___x_2524_);
                                crate::leanh::lean_ctor_set(v_q_2571_, 2, v_objectFieldKeys_2506_);
                                v___x_2572_ = l_Lean_Json_render___closed__15;
                                v___x_2573_ = lean_string_append(v_acc_2502_, v___x_2572_);
                                v___x_2574_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Data_Json_Printer_0__Lean_Json_compress_go_spec__1(v_q_2571_, v_kvPairs_2567_);
                                v_acc_2502_ = v___x_2573_;
                                v_q_2503_ = v___x_2574_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_q_2518_);
                        v___x_2576_ = crate::leanh::lean_box(0);
                        v___x_2577_ = lean_array_get_size(v_values_2505_);
                        v___x_2578_ = lean_nat_sub(v___x_2577_, v___x_2513_);
                        v_value_2579_ = lean_array_get(v___x_2576_, v_values_2505_, v___x_2578_);
                        crate::leanh::lean_dec(v___x_2578_);
                        v___x_2580_ = lean_array_get_size(v___x_2516_);
                        v___x_2581_ = lean_nat_dec_eq(v___x_2580_, v___x_2511_);
                        if v___x_2581_ == 0 {
                            v___x_2582_ = lean_array_pop(v_values_2505_);
                            v___x_2583_ = lean_nat_sub(v___x_2580_, v___x_2513_);
                            v_kind_2584_ = lean_array_fget(v___x_2516_, v___x_2583_);
                            crate::leanh::lean_dec(v___x_2583_);
                            v___x_2585_ = (crate::leanh::lean_unbox(v_kind_2584_) as u8);
                            crate::leanh::lean_dec(v_kind_2584_);
                            if v___x_2585_ == 2 {
                                v___x_2586_ = 0;
                                v___x_2587_ = crate::leanh::lean_box((v___x_2586_) as usize);
                                v___x_2588_ = lean_array_push(v___x_2516_, v___x_2587_);
                                v___x_2589_ = lean_array_push(v___x_2582_, v_value_2579_);
                                v___x_2590_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2590_, 0, v___x_2588_);
                                crate::leanh::lean_ctor_set(v___x_2590_, 1, v___x_2589_);
                                crate::leanh::lean_ctor_set(
                                    v___x_2590_,
                                    2,
                                    v_objectFieldKeys_2506_,
                                );
                                v_q_2503_ = v___x_2590_;
                                state = 0;
                                continue;
                            } else {
                                v___x_2592_ = 5;
                                v___x_2593_ = crate::leanh::lean_box((v___x_2592_) as usize);
                                v___x_2594_ = lean_array_push(v___x_2516_, v___x_2593_);
                                v___x_2595_ = 0;
                                v___x_2596_ = crate::leanh::lean_box((v___x_2595_) as usize);
                                v___x_2597_ = lean_array_push(v___x_2594_, v___x_2596_);
                                v___x_2598_ = lean_array_push(v___x_2582_, v_value_2579_);
                                v___x_2599_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2599_, 0, v___x_2597_);
                                crate::leanh::lean_ctor_set(v___x_2599_, 1, v___x_2598_);
                                crate::leanh::lean_ctor_set(
                                    v___x_2599_,
                                    2,
                                    v_objectFieldKeys_2506_,
                                );
                                v_q_2503_ = v___x_2599_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2516_);
                            crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                            crate::leanh::lean_dec_ref(v_values_2505_);
                            v___x_2601_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0;
                            v___x_2602_ = lean_mk_empty_array_with_capacity(v___x_2513_);
                            v___x_2603_ = lean_array_push(v___x_2602_, v_value_2579_);
                            v___x_2604_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1;
                            v___x_2605_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2605_, 0, v___x_2601_);
                            crate::leanh::lean_ctor_set(v___x_2605_, 1, v___x_2603_);
                            crate::leanh::lean_ctor_set(v___x_2605_, 2, v___x_2604_);
                            v_q_2503_ = v___x_2605_;
                            state = 0;
                            continue;
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v___x_2516_);
                        crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                        crate::leanh::lean_dec_ref(v_values_2505_);
                        v___x_2607_ = l_Lean_Json_render___closed__10;
                        v___x_2608_ = lean_string_append(v_acc_2502_, v___x_2607_);
                        v_acc_2502_ = v___x_2608_;
                        v_q_2503_ = v_q_2518_;
                        state = 0;
                        continue;
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v_q_2518_);
                        v___x_2610_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0;
                        v___x_2611_ = lean_array_get_size(v_objectFieldKeys_2506_);
                        v___x_2612_ = lean_nat_sub(v___x_2611_, v___x_2513_);
                        v_objectFieldKey_2613_ =
                            lean_array_get(v___x_2610_, v_objectFieldKeys_2506_, v___x_2612_);
                        crate::leanh::lean_dec(v___x_2612_);
                        v___x_2614_ = crate::leanh::lean_box(0);
                        v___x_2615_ = lean_array_get_size(v_values_2505_);
                        v___x_2616_ = lean_nat_sub(v___x_2615_, v___x_2513_);
                        v_value_2617_ = lean_array_get(v___x_2614_, v_values_2505_, v___x_2616_);
                        crate::leanh::lean_dec(v___x_2616_);
                        v___x_2628_ = lean_array_get_size(v___x_2516_);
                        v___x_2629_ = lean_nat_dec_eq(v___x_2628_, v___x_2511_);
                        if v___x_2629_ == 0 {
                            v___x_2630_ = lean_array_pop(v_objectFieldKeys_2506_);
                            v___x_2631_ = lean_array_pop(v_values_2505_);
                            v___x_2655_ = lean_nat_sub(v___x_2628_, v___x_2513_);
                            v_kind_2656_ = lean_array_fget(v___x_2516_, v___x_2655_);
                            crate::leanh::lean_dec(v___x_2655_);
                            v___x_2657_ = (crate::leanh::lean_unbox(v_kind_2656_) as u8);
                            crate::leanh::lean_dec(v_kind_2656_);
                            if v___x_2657_ == 4 {
                                v___x_2658_ = l_Lean_Json_renderString___closed__0;
                                v_acc_2659_ = lean_string_append(v_acc_2502_, v___x_2658_);
                                v___x_2660_ =
                                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(
                                        v_objectFieldKey_2613_,
                                    );
                                if v___x_2660_ == 0 {
                                    v___x_2661_ =
                                        lean_string_append(v_acc_2659_, v_objectFieldKey_2613_);
                                    crate::leanh::lean_dec(v_objectFieldKey_2613_);
                                    v___x_2662_ = lean_string_append(v___x_2661_, v___x_2658_);
                                    v___y_2646_ = v___x_2662_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_2663_ =
                                        lean_string_utf8_byte_size(v_objectFieldKey_2613_);
                                    crate::leanh::lean_inc(v_objectFieldKey_2613_);
                                    v___x_2664_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v___x_2664_,
                                        0,
                                        v_objectFieldKey_2613_,
                                    );
                                    crate::leanh::lean_ctor_set(v___x_2664_, 1, v___x_2511_);
                                    crate::leanh::lean_ctor_set(v___x_2664_, 2, v___x_2663_);
                                    v___x_2665_ = l_String_Slice_positions(v___x_2664_);
                                    v___x_2666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_2664_, v_objectFieldKey_2613_, v___x_2665_, v_acc_2659_);
                                    crate::leanh::lean_dec(v_objectFieldKey_2613_);
                                    crate::leanh::lean_dec_ref_known(v___x_2664_, 3);
                                    v___x_2667_ = lean_string_append(v___x_2666_, v___x_2658_);
                                    v___y_2646_ = v___x_2667_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v___x_2668_ = l_Lean_Json_renderString___closed__0;
                                v_acc_2669_ = lean_string_append(v_acc_2502_, v___x_2668_);
                                v___x_2670_ =
                                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(
                                        v_objectFieldKey_2613_,
                                    );
                                if v___x_2670_ == 0 {
                                    v___x_2671_ =
                                        lean_string_append(v_acc_2669_, v_objectFieldKey_2613_);
                                    crate::leanh::lean_dec(v_objectFieldKey_2613_);
                                    v___x_2672_ = lean_string_append(v___x_2671_, v___x_2668_);
                                    v___y_2633_ = v___x_2672_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_2673_ =
                                        lean_string_utf8_byte_size(v_objectFieldKey_2613_);
                                    crate::leanh::lean_inc(v_objectFieldKey_2613_);
                                    v___x_2674_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v___x_2674_,
                                        0,
                                        v_objectFieldKey_2613_,
                                    );
                                    crate::leanh::lean_ctor_set(v___x_2674_, 1, v___x_2511_);
                                    crate::leanh::lean_ctor_set(v___x_2674_, 2, v___x_2673_);
                                    v___x_2675_ = l_String_Slice_positions(v___x_2674_);
                                    v___x_2676_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_2674_, v_objectFieldKey_2613_, v___x_2675_, v_acc_2669_);
                                    crate::leanh::lean_dec(v_objectFieldKey_2613_);
                                    crate::leanh::lean_dec_ref_known(v___x_2674_, 3);
                                    v___x_2677_ = lean_string_append(v___x_2676_, v___x_2668_);
                                    v___y_2633_ = v___x_2677_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2516_);
                            crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                            crate::leanh::lean_dec_ref(v_values_2505_);
                            v___x_2678_ = l_Lean_Json_renderString___closed__0;
                            v_acc_2679_ = lean_string_append(v_acc_2502_, v___x_2678_);
                            v___x_2680_ =
                                l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(
                                    v_objectFieldKey_2613_,
                                );
                            if v___x_2680_ == 0 {
                                v___x_2681_ =
                                    lean_string_append(v_acc_2679_, v_objectFieldKey_2613_);
                                crate::leanh::lean_dec(v_objectFieldKey_2613_);
                                v___x_2682_ = lean_string_append(v___x_2681_, v___x_2678_);
                                v___y_2619_ = v___x_2682_;
                                state = 4;
                                continue;
                            } else {
                                v___x_2683_ = lean_string_utf8_byte_size(v_objectFieldKey_2613_);
                                crate::leanh::lean_inc(v_objectFieldKey_2613_);
                                v___x_2684_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2684_, 0, v_objectFieldKey_2613_);
                                crate::leanh::lean_ctor_set(v___x_2684_, 1, v___x_2511_);
                                crate::leanh::lean_ctor_set(v___x_2684_, 2, v___x_2683_);
                                v___x_2685_ = l_String_Slice_positions(v___x_2684_);
                                v___x_2686_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Json_render_spec__0___redArg(v___x_2684_, v_objectFieldKey_2613_, v___x_2685_, v_acc_2679_);
                                crate::leanh::lean_dec(v_objectFieldKey_2613_);
                                crate::leanh::lean_dec_ref_known(v___x_2684_, 3);
                                v___x_2687_ = lean_string_append(v___x_2686_, v___x_2678_);
                                v___y_2619_ = v___x_2687_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v___x_2516_);
                        crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                        crate::leanh::lean_dec_ref(v_values_2505_);
                        v___x_2688_ = l_Lean_Json_render___closed__16;
                        v___x_2689_ = lean_string_append(v_acc_2502_, v___x_2688_);
                        v_acc_2502_ = v___x_2689_;
                        v_q_2503_ = v_q_2518_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___x_2516_);
                        crate::leanh::lean_dec_ref(v_objectFieldKeys_2506_);
                        crate::leanh::lean_dec_ref(v_values_2505_);
                        v___x_2691_ = l_Lean_Json_render___closed__6;
                        v___x_2692_ = lean_string_append(v_acc_2502_, v___x_2691_);
                        v_acc_2502_ = v___x_2692_;
                        v_q_2503_ = v_q_2518_;
                        state = 0;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2528_ = lean_string_append(v_acc_2502_, v___y_2527_);
                v_acc_2502_ = v___x_2528_;
                v_q_2503_ = v_q_2525_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2620_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0;
                v___x_2621_ = lean_string_append(v___y_2619_, v___x_2620_);
                v___x_2622_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__0;
                v___x_2623_ = lean_mk_empty_array_with_capacity(v___x_2513_);
                v___x_2624_ = lean_array_push(v___x_2623_, v_value_2617_);
                v___x_2625_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1;
                v___x_2626_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2626_, 0, v___x_2622_);
                crate::leanh::lean_ctor_set(v___x_2626_, 1, v___x_2624_);
                crate::leanh::lean_ctor_set(v___x_2626_, 2, v___x_2625_);
                v_acc_2502_ = v___x_2621_;
                v_q_2503_ = v___x_2626_;
                state = 0;
                continue;
            }
            5 => {
                v___x_2634_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0;
                v___x_2635_ = lean_string_append(v___y_2633_, v___x_2634_);
                v___x_2636_ = 5;
                v___x_2637_ = crate::leanh::lean_box((v___x_2636_) as usize);
                v___x_2638_ = lean_array_push(v___x_2516_, v___x_2637_);
                v___x_2639_ = 0;
                v___x_2640_ = crate::leanh::lean_box((v___x_2639_) as usize);
                v___x_2641_ = lean_array_push(v___x_2638_, v___x_2640_);
                v___x_2642_ = lean_array_push(v___x_2631_, v_value_2617_);
                v___x_2643_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2643_, 0, v___x_2641_);
                crate::leanh::lean_ctor_set(v___x_2643_, 1, v___x_2642_);
                crate::leanh::lean_ctor_set(v___x_2643_, 2, v___x_2630_);
                v_acc_2502_ = v___x_2635_;
                v_q_2503_ = v___x_2643_;
                state = 0;
                continue;
            }
            6 => {
                v___x_2647_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_render_spec__4_spec__5___closed__0;
                v___x_2648_ = lean_string_append(v___y_2646_, v___x_2647_);
                v___x_2649_ = 0;
                v___x_2650_ = crate::leanh::lean_box((v___x_2649_) as usize);
                v___x_2651_ = lean_array_push(v___x_2516_, v___x_2650_);
                v___x_2652_ = lean_array_push(v___x_2631_, v_value_2617_);
                v___x_2653_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2653_, 0, v___x_2651_);
                crate::leanh::lean_ctor_set(v___x_2653_, 1, v___x_2652_);
                crate::leanh::lean_ctor_set(v___x_2653_, 2, v___x_2630_);
                v_acc_2502_ = v___x_2648_;
                v_q_2503_ = v___x_2653_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_compress(
    mut v_j_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_CompressWorkItemQueue_popObjectFieldKey_x21___closed__0;
    v___x_2703_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2704_ = lean_mk_empty_array_with_capacity(v___x_2703_);
    v___x_2705_ = l_Lean_Json_compress___closed__0;
    v___x_2706_ = lean_array_push(v___x_2704_, v_j_2701_);
    v___x_2707_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go___closed__1;
    v___x_2708_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2705_);
    crate::leanh::lean_ctor_set(v___x_2708_, 1, v___x_2706_);
    crate::leanh::lean_ctor_set(v___x_2708_, 2, v___x_2707_);
    v___x_2709_ =
        l___private_Lean_Data_Json_Printer_0__Lean_Json_compress_go(v___x_2702_, v___x_2708_);
    return v___x_2709_;
}
pub unsafe fn l_Lean_Json_instToString___lam__0(
    mut v_j_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = crate::leanh::lean_unsigned_to_nat(80);
    v___x_2714_ = l_Lean_Json_pretty(v_j_2712_, v___x_2713_);
    return v___x_2714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_Printer(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_Printer(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_Printer(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Json_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Printer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_Printer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Json_Printer(builtin);
}
