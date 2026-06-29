// Lean compiler output
// Module: Lean.AuxRecursor
// Imports: Lean.EnvExtension Init.Data.String.TakeDrop
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_MapDeclarationExtension_contains___redArg,
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_TagDeclarationExtension_isTagged,
    l_Lean_TagDeclarationExtension_tag, l_Lean_mkMapDeclarationExtension___redArg,
    l_Lean_mkTagDeclarationExtension, runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::ffi::lean_array_uget_borrowed;
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_memcmp;
use crate::ffi::{lean_usize_add, lean_usize_of_nat};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
pub static l_Lean_casesOnSuffix___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 97, 115, 101, 115, 79, 110, 0],
    };
static mut l_Lean_casesOnSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_casesOnSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_casesOnSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_casesOnSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recOnSuffix___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [114, 101, 99, 79, 110, 0],
    };
static mut l_Lean_recOnSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_recOnSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_recOnSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_recOnSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_brecOnSuffix___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [98, 114, 101, 99, 79, 110, 0],
    };
static mut l_Lean_brecOnSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_brecOnSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_brecOnSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_brecOnSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_belowSuffix___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [98, 101, 108, 111, 119, 0],
    };
static mut l_Lean_belowSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_belowSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_belowSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_belowSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 117, 120, 82, 101, 99, 69, 120, 116, 0]};
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3832961945475411305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_auxRecExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_isAuxRecursor___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_isAuxRecursor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isAuxRecursor___closed__1_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [110, 100, 114, 101, 99, 95, 115, 121, 109, 109, 0],
    };
static mut l_Lean_isAuxRecursor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_isAuxRecursor___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_isAuxRecursor___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__1_value)
                as *mut crate::leanh::LeanObject,
            12046918839254097991 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isAuxRecursor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isAuxRecursor___closed__3_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [110, 100, 114, 101, 99, 79, 110, 0],
    };
static mut l_Lean_isAuxRecursor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_isAuxRecursor___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_isAuxRecursor___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__3_value)
                as *mut crate::leanh::LeanObject,
            15352662879234479178 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isAuxRecursor___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isAuxRecursor___closed__5_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [110, 100, 114, 101, 99, 0],
    };
static mut l_Lean_isAuxRecursor___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_isAuxRecursor___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_isAuxRecursor___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__5_value)
                as *mut crate::leanh::LeanObject,
            12920047613083624563 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isAuxRecursor___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursor___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isAuxRecursorWithSuffix___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [95, 0],
    };
static mut l_Lean_isAuxRecursorWithSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isAuxRecursorWithSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [65, 117, 120, 82, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8205767672292198387 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__4_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13988194838545651550 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__5_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10234282300872036775 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 112, 97, 114, 115, 101, 67, 97, 115, 101, 115, 79, 110, 69, 120, 116, 0]};
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__6_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__7_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13951987296346176704 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_instInhabitedNoConfusionInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedNoConfusionInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedNoConfusionInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedNoConfusionInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 67, 111, 110, 102, 117, 115, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15249345684164379690 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_noConfusionExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getNoConfusionInfo___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Lean_getNoConfusionInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getNoConfusionInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getNoConfusionInfo___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Lean_getNoConfusionInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getNoConfusionInfo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getNoConfusionInfo___closed__2_value: crate::leanh::LeanStringObject<14> =
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
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_getNoConfusionInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getNoConfusionInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getNoConfusionInfo___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getNoConfusionInfo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_mkCasesOnName(
    mut v_indDeclName_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = l_Lean_casesOnSuffix___closed__0;
    v___x_343_ = l_Lean_Name_str___override(v_indDeclName_341_, v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_Lean_mkRecOnName(
    mut v_indDeclName_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = l_Lean_recOnSuffix___closed__0;
    v___x_346_ = l_Lean_Name_str___override(v_indDeclName_344_, v___x_345_);
    return v___x_346_;
}
pub unsafe fn l_Lean_mkBRecOnName(
    mut v_indDeclName_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = l_Lean_brecOnSuffix___closed__0;
    v___x_349_ = l_Lean_Name_str___override(v_indDeclName_347_, v___x_348_);
    return v___x_349_;
}
pub unsafe fn l_Lean_mkBelowName(
    mut v_indDeclName_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = l_Lean_belowSuffix___closed__0;
    v___x_352_ = l_Lean_Name_str___override(v_indDeclName_350_, v___x_351_);
    return v___x_352_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_361_ = l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_;
    v___x_362_ = l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_;
    v___x_363_ = l_Lean_mkTagDeclarationExtension(v___x_361_, v___x_362_);
    return v___x_363_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2____boxed(
    mut v_a_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_365_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_();
    return v_res_365_;
}
pub unsafe fn l_Lean_markAuxRecursor(
    mut v_env_366_: *mut crate::leanh::LeanObject,
    mut v_declName_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Lean_auxRecExt;
    v___x_369_ = l_Lean_TagDeclarationExtension_tag(v___x_368_, v_env_366_, v_declName_367_);
    return v___x_369_;
}
pub unsafe fn l_Lean_isAuxRecursor(
    mut v_env_383_: *mut crate::leanh::LeanObject,
    mut v_declName_384_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_386_: u8 = 0;
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: u8 = 0;
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: u8 = 0;
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_391_ = l_Lean_auxRecExt;
                v_toEnvExtension_392_ = crate::leanh::lean_ctor_get(v___x_391_, 0);
                v_asyncMode_393_ = crate::leanh::lean_ctor_get(v_toEnvExtension_392_, 2);
                crate::leanh::lean_inc(v_declName_384_);
                v___x_394_ = l_Lean_TagDeclarationExtension_isTagged(
                    v___x_391_,
                    v_env_383_,
                    v_declName_384_,
                    v_asyncMode_393_,
                );
                if v___x_394_ == 0 {
                    v___x_395_ = l_Lean_isAuxRecursor___closed__6;
                    v___x_396_ = lean_name_eq(v_declName_384_, v___x_395_);
                    v___y_386_ = v___x_396_;
                    state = 1;
                    continue;
                } else {
                    v___y_386_ = v___x_394_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_386_ == 0 {
                    v___x_387_ = l_Lean_isAuxRecursor___closed__2;
                    v___x_388_ = lean_name_eq(v_declName_384_, v___x_387_);
                    if v___x_388_ == 0 {
                        v___x_389_ = l_Lean_isAuxRecursor___closed__4;
                        v___x_390_ = lean_name_eq(v_declName_384_, v___x_389_);
                        crate::leanh::lean_dec(v_declName_384_);
                        return v___x_390_;
                    } else {
                        crate::leanh::lean_dec(v_declName_384_);
                        return v___x_388_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_384_);
                    return v___y_386_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isAuxRecursor___boxed(
    mut v_env_397_: *mut crate::leanh::LeanObject,
    mut v_declName_398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_399_: u8 = 0;
    let mut v_r_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Lean_isAuxRecursor(v_env_397_, v_declName_398_);
    v_r_400_ = crate::leanh::lean_box((v_res_399_) as usize);
    return v_r_400_;
}
pub unsafe fn l_Lean_isAuxRecursorWithSuffix(
    mut v_env_402_: *mut crate::leanh::LeanObject,
    mut v_declName_403_: *mut crate::leanh::LeanObject,
    mut v_suffix_404_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_406_: u8 = 0;
    let mut v___x_407_: u8 = 0;
    let mut v_str_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: u8 = 0;
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: u8 = 0;
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: u8 = 0;
    let mut v___x_417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_declName_403_) == 1 {
                    v_str_408_ = crate::leanh::lean_ctor_get(v_declName_403_, 1);
                    v___x_409_ = lean_string_dec_eq(v_str_408_, v_suffix_404_);
                    if v___x_409_ == 0 {
                        v___x_410_ = l_Lean_isAuxRecursorWithSuffix___closed__0;
                        v___x_411_ = lean_string_append(v_suffix_404_, v___x_410_);
                        v___x_412_ = lean_string_utf8_byte_size(v_str_408_);
                        v___x_413_ = lean_string_utf8_byte_size(v___x_411_);
                        v___x_414_ = lean_nat_dec_le(v___x_413_, v___x_412_);
                        if v___x_414_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_411_);
                            v___y_406_ = v___x_409_;
                            state = 1;
                            continue;
                        } else {
                            v___x_415_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_416_ = lean_string_memcmp(
                                v_str_408_, v___x_411_, v___x_415_, v___x_415_, v___x_413_,
                            );
                            crate::leanh::lean_dec_ref(v___x_411_);
                            v___y_406_ = v___x_416_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_suffix_404_);
                        v___y_406_ = v___x_409_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_suffix_404_);
                    crate::leanh::lean_dec(v_declName_403_);
                    crate::leanh::lean_dec_ref(v_env_402_);
                    v___x_417_ = 0;
                    return v___x_417_;
                }
            }
            1 => {
                if v___y_406_ == 0 {
                    crate::leanh::lean_dec(v_declName_403_);
                    crate::leanh::lean_dec_ref(v_env_402_);
                    return v___y_406_;
                } else {
                    v___x_407_ = l_Lean_isAuxRecursor(v_env_402_, v_declName_403_);
                    return v___x_407_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isAuxRecursorWithSuffix___boxed(
    mut v_env_418_: *mut crate::leanh::LeanObject,
    mut v_declName_419_: *mut crate::leanh::LeanObject,
    mut v_suffix_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_421_: u8 = 0;
    let mut v_r_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Lean_isAuxRecursorWithSuffix(v_env_418_, v_declName_419_, v_suffix_420_);
    v_r_422_ = crate::leanh::lean_box((v_res_421_) as usize);
    return v_r_422_;
}
pub unsafe fn l_Lean_isCasesOnRecursor(
    mut v_env_423_: *mut crate::leanh::LeanObject,
    mut v_declName_424_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    v___x_425_ = l_Lean_casesOnSuffix___closed__0;
    v___x_426_ = l_Lean_isAuxRecursorWithSuffix(v_env_423_, v_declName_424_, v___x_425_);
    return v___x_426_;
}
pub unsafe fn l_Lean_isCasesOnRecursor___boxed(
    mut v_env_427_: *mut crate::leanh::LeanObject,
    mut v_declName_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_429_: u8 = 0;
    let mut v_r_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Lean_isCasesOnRecursor(v_env_427_, v_declName_428_);
    v_r_430_ = crate::leanh::lean_box((v_res_429_) as usize);
    return v_r_430_;
}
pub unsafe fn l_Lean_isRecOnRecursor(
    mut v_env_431_: *mut crate::leanh::LeanObject,
    mut v_declName_432_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: u8 = 0;
    v___x_433_ = l_Lean_recOnSuffix___closed__0;
    v___x_434_ = l_Lean_isAuxRecursorWithSuffix(v_env_431_, v_declName_432_, v___x_433_);
    return v___x_434_;
}
pub unsafe fn l_Lean_isRecOnRecursor___boxed(
    mut v_env_435_: *mut crate::leanh::LeanObject,
    mut v_declName_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_437_: u8 = 0;
    let mut v_r_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_437_ = l_Lean_isRecOnRecursor(v_env_435_, v_declName_436_);
    v_r_438_ = crate::leanh::lean_box((v_res_437_) as usize);
    return v_r_438_;
}
pub unsafe fn l_Lean_isBRecOnRecursor(
    mut v_env_439_: *mut crate::leanh::LeanObject,
    mut v_declName_440_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: u8 = 0;
    v___x_441_ = l_Lean_brecOnSuffix___closed__0;
    v___x_442_ = l_Lean_isAuxRecursorWithSuffix(v_env_439_, v_declName_440_, v___x_441_);
    return v___x_442_;
}
pub unsafe fn l_Lean_isBRecOnRecursor___boxed(
    mut v_env_443_: *mut crate::leanh::LeanObject,
    mut v_declName_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_445_: u8 = 0;
    let mut v_r_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_445_ = l_Lean_isBRecOnRecursor(v_env_443_, v_declName_444_);
    v_r_446_ = crate::leanh::lean_box((v_res_445_) as usize);
    return v_r_446_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = l___private_Lean_AuxRecursor_0__Lean_initFn___closed__8_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_;
    v___x_470_ = l___private_Lean_AuxRecursor_0__Lean_initFn___closed__3_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_;
    v___x_471_ = l_Lean_mkTagDeclarationExtension(v___x_469_, v___x_470_);
    return v___x_471_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2____boxed(
    mut v_a_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_473_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_();
    return v_res_473_;
}
pub unsafe fn l_Lean_markSparseCasesOn(
    mut v_env_474_: *mut crate::leanh::LeanObject,
    mut v_declName_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
    v___x_477_ = l_Lean_TagDeclarationExtension_tag(v___x_476_, v_env_474_, v_declName_475_);
    return v___x_477_;
}
pub unsafe fn l_Lean_isSparseCasesOn(
    mut v_env_478_: *mut crate::leanh::LeanObject,
    mut v_declName_479_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: u8 = 0;
    v___x_480_ = l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt;
    v_toEnvExtension_481_ = crate::leanh::lean_ctor_get(v___x_480_, 0);
    v_asyncMode_482_ = crate::leanh::lean_ctor_get(v_toEnvExtension_481_, 2);
    v___x_483_ = l_Lean_TagDeclarationExtension_isTagged(
        v___x_480_,
        v_env_478_,
        v_declName_479_,
        v_asyncMode_482_,
    );
    return v___x_483_;
}
pub unsafe fn l_Lean_isSparseCasesOn___boxed(
    mut v_env_484_: *mut crate::leanh::LeanObject,
    mut v_declName_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_486_: u8 = 0;
    let mut v_r_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_486_ = l_Lean_isSparseCasesOn(v_env_484_, v_declName_485_);
    v_r_487_ = crate::leanh::lean_box((v_res_486_) as usize);
    return v_r_487_;
}
pub unsafe fn l_Lean_isCasesOnLike(
    mut v_env_488_: *mut crate::leanh::LeanObject,
    mut v_declName_489_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_490_: u8 = 0;
    crate::leanh::lean_inc(v_declName_489_);
    crate::leanh::lean_inc_ref(v_env_488_);
    v___x_490_ = l_Lean_isCasesOnRecursor(v_env_488_, v_declName_489_);
    if v___x_490_ == 0 {
        let mut v___x_491_: u8 = 0;
        v___x_491_ = l_Lean_isSparseCasesOn(v_env_488_, v_declName_489_);
        return v___x_491_;
    } else {
        crate::leanh::lean_dec(v_declName_489_);
        crate::leanh::lean_dec_ref(v_env_488_);
        return v___x_490_;
    }
}
pub unsafe fn l_Lean_isCasesOnLike___boxed(
    mut v_env_492_: *mut crate::leanh::LeanObject,
    mut v_declName_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_494_: u8 = 0;
    let mut v_r_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Lean_isCasesOnLike(v_env_492_, v_declName_493_);
    v_r_495_ = crate::leanh::lean_box((v_res_494_) as usize);
    return v_r_495_;
}
pub unsafe fn l_Lean_NoConfusionInfo_ctorIdx(
    mut v_x_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_496_) == 0 {
        let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_497_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_497_;
    } else {
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_498_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_498_;
    }
}
pub unsafe fn l_Lean_NoConfusionInfo_ctorIdx___boxed(
    mut v_x_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_500_ = l_Lean_NoConfusionInfo_ctorIdx(v_x_499_);
    crate::leanh::lean_dec_ref(v_x_499_);
    return v_res_500_;
}
pub unsafe fn l_Lean_NoConfusionInfo_ctorElim___redArg(
    mut v_t_501_: *mut crate::leanh::LeanObject,
    mut v_k_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_501_) == 0 {
        let mut v_arity_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_arity_503_ = crate::leanh::lean_ctor_get(v_t_501_, 0);
        crate::leanh::lean_inc(v_arity_503_);
        v_lhs_504_ = crate::leanh::lean_ctor_get(v_t_501_, 1);
        crate::leanh::lean_inc(v_lhs_504_);
        v_rhs_505_ = crate::leanh::lean_ctor_get(v_t_501_, 2);
        crate::leanh::lean_inc(v_rhs_505_);
        crate::leanh::lean_dec_ref_known(v_t_501_, 3);
        v___x_506_ = crate::leanh::lean_apply_3(v_k_502_, v_arity_503_, v_lhs_504_, v_rhs_505_);
        return v___x_506_;
    } else {
        let mut v_arity_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fields_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_arity_507_ = crate::leanh::lean_ctor_get(v_t_501_, 0);
        crate::leanh::lean_inc(v_arity_507_);
        v_fields_508_ = crate::leanh::lean_ctor_get(v_t_501_, 1);
        crate::leanh::lean_inc(v_fields_508_);
        crate::leanh::lean_dec_ref_known(v_t_501_, 2);
        v___x_509_ = crate::leanh::lean_apply_2(v_k_502_, v_arity_507_, v_fields_508_);
        return v___x_509_;
    }
}
pub unsafe fn l_Lean_NoConfusionInfo_ctorElim(
    mut v_motive_510_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_511_: *mut crate::leanh::LeanObject,
    mut v_t_512_: *mut crate::leanh::LeanObject,
    mut v_h_513_: *mut crate::leanh::LeanObject,
    mut v_k_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_515_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_512_, v_k_514_);
    return v___x_515_;
}
pub unsafe fn l_Lean_NoConfusionInfo_ctorElim___boxed(
    mut v_motive_516_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_517_: *mut crate::leanh::LeanObject,
    mut v_t_518_: *mut crate::leanh::LeanObject,
    mut v_h_519_: *mut crate::leanh::LeanObject,
    mut v_k_520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_521_ = l_Lean_NoConfusionInfo_ctorElim(
        v_motive_516_,
        v_ctorIdx_517_,
        v_t_518_,
        v_h_519_,
        v_k_520_,
    );
    crate::leanh::lean_dec(v_ctorIdx_517_);
    return v_res_521_;
}
pub unsafe fn l_Lean_NoConfusionInfo_regular_elim___redArg(
    mut v_t_522_: *mut crate::leanh::LeanObject,
    mut v_regular_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_522_, v_regular_523_);
    return v___x_524_;
}
pub unsafe fn l_Lean_NoConfusionInfo_regular_elim(
    mut v_motive_525_: *mut crate::leanh::LeanObject,
    mut v_t_526_: *mut crate::leanh::LeanObject,
    mut v_h_527_: *mut crate::leanh::LeanObject,
    mut v_regular_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_526_, v_regular_528_);
    return v___x_529_;
}
pub unsafe fn l_Lean_NoConfusionInfo_perCtor_elim___redArg(
    mut v_t_530_: *mut crate::leanh::LeanObject,
    mut v_perCtor_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_532_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_530_, v_perCtor_531_);
    return v___x_532_;
}
pub unsafe fn l_Lean_NoConfusionInfo_perCtor_elim(
    mut v_motive_533_: *mut crate::leanh::LeanObject,
    mut v_t_534_: *mut crate::leanh::LeanObject,
    mut v_h_535_: *mut crate::leanh::LeanObject,
    mut v_perCtor_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = l_Lean_NoConfusionInfo_ctorElim___redArg(v_t_534_, v_perCtor_536_);
    return v___x_537_;
}
pub unsafe fn l_Lean_NoConfusionInfo_arity(
    mut v_x_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_arity_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_arity_543_ = crate::leanh::lean_ctor_get(v_x_542_, 0);
    crate::leanh::lean_inc(v_arity_543_);
    return v_arity_543_;
}
pub unsafe fn l_Lean_NoConfusionInfo_arity___boxed(
    mut v_x_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_NoConfusionInfo_arity(v_x_544_);
    crate::leanh::lean_dec_ref(v_x_544_);
    return v_res_545_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_546_: *mut crate::leanh::LeanObject,
    mut v_x_547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_547_) == 0 {
                    v_k_548_ = crate::leanh::lean_ctor_get(v_x_547_, 1);
                    v_v_549_ = crate::leanh::lean_ctor_get(v_x_547_, 2);
                    v_l_550_ = crate::leanh::lean_ctor_get(v_x_547_, 3);
                    v_r_551_ = crate::leanh::lean_ctor_get(v_x_547_, 4);
                    v___x_552_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v_init_546_, v_l_550_);
                    crate::leanh::lean_inc(v_v_549_);
                    crate::leanh::lean_inc(v_k_548_);
                    v___x_553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_553_, 0, v_k_548_);
                    crate::leanh::lean_ctor_set(v___x_553_, 1, v_v_549_);
                    v___x_554_ = lean_array_push(v___x_552_, v___x_553_);
                    v_init_546_ = v___x_554_;
                    v_x_547_ = v_r_551_;
                    state = 0;
                    continue;
                } else {
                    return v_init_546_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_556_: *mut crate::leanh::LeanObject,
    mut v_x_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v_init_556_, v_x_557_);
    crate::leanh::lean_dec(v_x_557_);
    return v_res_558_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(
    mut v_env_559_: *mut crate::leanh::LeanObject,
    mut v_as_560_: *mut crate::leanh::LeanObject,
    mut v_i_561_: usize,
    mut v_stop_562_: usize,
    mut v_b_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: usize = 0;
    let mut v___x_567_: usize = 0;
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: u8 = 0;
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_569_ = lean_usize_dec_eq(v_i_561_, v_stop_562_);
                if v___x_569_ == 0 {
                    v___x_570_ = lean_array_uget_borrowed(v_as_560_, v_i_561_);
                    v_fst_571_ = crate::leanh::lean_ctor_get(v___x_570_, 0);
                    crate::leanh::lean_inc(v_fst_571_);
                    crate::leanh::lean_inc_ref(v_env_559_);
                    v___x_572_ = l_Lean_Environment_contains(v_env_559_, v_fst_571_, v___x_569_);
                    if v___x_572_ == 0 {
                        v___y_565_ = v_b_563_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_570_);
                        v___x_573_ = lean_array_push(v_b_563_, v___x_570_);
                        v___y_565_ = v___x_573_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_559_);
                    return v_b_563_;
                }
            }
            1 => {
                v___x_566_ = 1usize;
                v___x_567_ = lean_usize_add(v_i_561_, v___x_566_);
                v_i_561_ = v___x_567_;
                v_b_563_ = v___y_565_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_574_: *mut crate::leanh::LeanObject,
    mut v_as_575_: *mut crate::leanh::LeanObject,
    mut v_i_576_: *mut crate::leanh::LeanObject,
    mut v_stop_577_: *mut crate::leanh::LeanObject,
    mut v_b_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_579_: usize = 0;
    let mut v_stop_boxed_580_: usize = 0;
    let mut v_res_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_579_ = crate::leanh::lean_unbox_usize(v_i_576_);
    crate::leanh::lean_dec(v_i_576_);
    v_stop_boxed_580_ = crate::leanh::lean_unbox_usize(v_stop_577_);
    crate::leanh::lean_dec(v_stop_577_);
    v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(v_env_574_, v_as_575_, v_i_boxed_579_, v_stop_boxed_580_, v_b_578_);
    crate::leanh::lean_dec_ref(v_as_575_);
    return v_res_581_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_(
    mut v_env_588_: *mut crate::leanh::LeanObject,
    mut v_s_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    v___x_590_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_591_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_;
    v___x_592_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v___x_591_, v_s_589_);
    v___x_593_ = lean_array_get_size(v___x_592_);
    v___x_594_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_;
    v___x_595_ = lean_nat_dec_lt(v___x_590_, v___x_593_);
    if v___x_595_ == 0 {
        let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_592_);
        crate::leanh::lean_dec_ref(v_env_588_);
        v___x_596_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_;
        return v___x_596_;
    } else {
        let mut v___x_597_: u8 = 0;
        v___x_597_ = lean_nat_dec_le(v___x_593_, v___x_593_);
        if v___x_597_ == 0 {
            if v___x_595_ == 0 {
                let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_592_);
                crate::leanh::lean_dec_ref(v_env_588_);
                v___x_598_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_;
                return v___x_598_;
            } else {
                let mut v___x_599_: usize = 0;
                let mut v___x_600_: usize = 0;
                let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_599_ = 0usize;
                v___x_600_ = lean_usize_of_nat(v___x_593_);
                v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(v_env_588_, v___x_592_, v___x_599_, v___x_600_, v___x_594_);
                crate::leanh::lean_dec_ref(v___x_592_);
                crate::leanh::lean_inc_ref_n(v___x_601_, 2);
                v___x_602_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_602_, 0, v___x_601_);
                crate::leanh::lean_ctor_set(v___x_602_, 1, v___x_601_);
                crate::leanh::lean_ctor_set(v___x_602_, 2, v___x_601_);
                return v___x_602_;
            }
        } else {
            let mut v___x_603_: usize = 0;
            let mut v___x_604_: usize = 0;
            let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_603_ = 0usize;
            v___x_604_ = lean_usize_of_nat(v___x_593_);
            v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__1(v_env_588_, v___x_592_, v___x_603_, v___x_604_, v___x_594_);
            crate::leanh::lean_dec_ref(v___x_592_);
            crate::leanh::lean_inc_ref_n(v___x_605_, 2);
            v___x_606_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_606_, 0, v___x_605_);
            crate::leanh::lean_ctor_set(v___x_606_, 1, v___x_605_);
            crate::leanh::lean_ctor_set(v___x_606_, 2, v___x_605_);
            return v___x_606_;
        }
    }
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed(
    mut v_env_607_: *mut crate::leanh::LeanObject,
    mut v_s_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l___private_Lean_AuxRecursor_0__Lean_initFn___lam__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_(v_env_607_, v_s_608_);
    crate::leanh::lean_dec(v_s_608_);
    return v_res_609_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_616_ = l___private_Lean_AuxRecursor_0__Lean_initFn___closed__0_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_;
    v___x_617_ = l___private_Lean_AuxRecursor_0__Lean_initFn___closed__2_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_;
    v___x_618_ = crate::leanh::lean_box(2);
    v___x_619_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_617_, v___x_618_, v___f_616_);
    return v___x_619_;
}
pub unsafe fn l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2____boxed(
    mut v_a_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_();
    return v_res_621_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0(
    mut v_init_622_: *mut crate::leanh::LeanObject,
    mut v_t_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0_spec__0(v_init_622_, v_t_623_);
    return v___x_624_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_625_: *mut crate::leanh::LeanObject,
    mut v_t_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_627_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2__spec__0(v_init_625_, v_t_626_);
    crate::leanh::lean_dec(v_t_626_);
    return v_res_627_;
}
pub unsafe fn l_Lean_markNoConfusion(
    mut v_env_628_: *mut crate::leanh::LeanObject,
    mut v_n_629_: *mut crate::leanh::LeanObject,
    mut v_info_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_noConfusionExt;
    v___x_632_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_631_,
        v_env_628_,
        v_n_629_,
        v_info_630_,
    );
    return v___x_632_;
}
pub unsafe fn l_Lean_isNoConfusion(
    mut v_env_633_: *mut crate::leanh::LeanObject,
    mut v_n_634_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u8 = 0;
    v___x_635_ = l_Lean_instInhabitedNoConfusionInfo_default;
    v___x_636_ = l_Lean_noConfusionExt;
    v___x_637_ = l_Lean_MapDeclarationExtension_contains___redArg(
        v___x_635_, v___x_636_, v_env_633_, v_n_634_,
    );
    return v___x_637_;
}
pub unsafe fn l_Lean_isNoConfusion___boxed(
    mut v_env_638_: *mut crate::leanh::LeanObject,
    mut v_n_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_640_: u8 = 0;
    let mut v_r_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Lean_isNoConfusion(v_env_638_, v_n_639_);
    v_r_641_ = crate::leanh::lean_box((v_res_640_) as usize);
    return v_r_641_;
}
pub unsafe fn l_panic___at___00Lean_getNoConfusionInfo_spec__0(
    mut v_msg_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l_Lean_instInhabitedNoConfusionInfo_default;
    v___x_644_ = lean_panic_fn_borrowed(v___x_643_, v_msg_642_);
    return v___x_644_;
}
pub unsafe fn _init_l_Lean_getNoConfusionInfo___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_648_ = l_Lean_getNoConfusionInfo___closed__2;
    v___x_649_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_650_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_651_ = l_Lean_getNoConfusionInfo___closed__1;
    v___x_652_ = l_Lean_getNoConfusionInfo___closed__0;
    v___x_653_ =
        l_mkPanicMessageWithDecl(v___x_652_, v___x_651_, v___x_650_, v___x_649_, v___x_648_);
    return v___x_653_;
}
pub unsafe fn l_Lean_getNoConfusionInfo(
    mut v_env_654_: *mut crate::leanh::LeanObject,
    mut v_n_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: u8 = 0;
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = l_Lean_noConfusionExt;
    v_toEnvExtension_657_ = crate::leanh::lean_ctor_get(v___x_656_, 0);
    v_asyncMode_658_ = crate::leanh::lean_ctor_get(v_toEnvExtension_657_, 2);
    v___x_659_ = l_Lean_instInhabitedNoConfusionInfo_default;
    v___x_660_ = 0;
    v___x_661_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_659_,
        v___x_656_,
        v_env_654_,
        v_n_655_,
        v_asyncMode_658_,
        v___x_660_,
    );
    if crate::leanh::lean_obj_tag(v___x_661_) == 0 {
        let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_662_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_getNoConfusionInfo___closed__3),
            core::ptr::addr_of_mut!(l_Lean_getNoConfusionInfo___closed__3_once),
            _init_l_Lean_getNoConfusionInfo___closed__3,
        );
        v___x_663_ = l_panic___at___00Lean_getNoConfusionInfo_spec__0(v___x_662_);
        return v___x_663_;
    } else {
        let mut v_val_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_664_ = crate::leanh::lean_ctor_get(v___x_661_, 0);
        crate::leanh::lean_inc(v_val_664_);
        crate::leanh::lean_dec_ref_known(v___x_661_, 1);
        return v_val_664_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_AuxRecursor(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_3890270560____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_auxRecExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_auxRecExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_235549338____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_AuxRecursor_0__Lean_sparseCasesOnExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_AuxRecursor_0__Lean_initFn_00___x40_Lean_AuxRecursor_1899236304____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_noConfusionExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_noConfusionExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_AuxRecursor(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_AuxRecursor(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_AuxRecursor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_AuxRecursor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_AuxRecursor(builtin);
}
