// Lean compiler output
// Module: Init.Data.Range.Polymorphic.PRange
// Imports: Init.Data.Range.Polymorphic.UpwardEnumerable
use crate::r#gen::Init::Data::Range::Polymorphic::UpwardEnumerable::{
    initialize_Init_Data_Range_Polymorphic_UpwardEnumerable,
    runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [83, 116, 100, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 95, 46, 46, 46, 42, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e_x2a___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__1_value)
                as *mut crate::leanh::LeanObject,
            12901981646182791257 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [46, 46, 46, 42, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e_x2a: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 42, 46, 46, 46, 42, 0],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15812821569646102790 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [42, 46, 46, 46, 42, 0],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e_x2a: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 42, 0],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18313290646982499243 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [60, 46, 46, 46, 42, 0],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e_x2a: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 46, 46, 46, 60, 95, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            4456104206502475912 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [46, 46, 46, 60, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e_x3c__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 95, 46, 46, 46, 95, 0],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394156637022377744 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [46, 46, 46, 0],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 101, 114, 109, 42, 46, 46, 46, 60, 95, 0],
};
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            17665753292882927436 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [42, 46, 46, 46, 60, 0],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e_x3c__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 101, 114, 109, 42, 46, 46, 46, 95, 0],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            10703712094186559148 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [42, 46, 46, 46, 0],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 60, 95, 0],
};
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            17893611459657078921 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [60, 46, 46, 46, 60, 0],
};
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e_x3c__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 95, 0],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            3473794126537410698 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [60, 46, 46, 46, 0],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 101, 114, 109, 95, 46, 46, 46, 61, 95, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            8312988086032421140 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [46, 46, 46, 61, 0],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e_x3d__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 101, 114, 109, 42, 46, 46, 46, 61, 95, 0],
};
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            897828399751270016 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [42, 46, 46, 46, 61, 0],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e_x3d__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 101, 114, 109, 95, 60, 46, 46, 46, 61, 95, 0],
};
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value)
                as *mut crate::leanh::LeanObject,
            15212140180363167796 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [60, 46, 46, 46, 61, 0],
};
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e_x3d__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 99, 99, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject,16265292064117835183 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,8855140571667196803 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject,16437420457889295896 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,15874481382248158464 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 99, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject,16004387948037561718 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,7181152285640718342 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject,8649810267064386489 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,8380740754681987765 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 99, 105, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 105, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,6989692408478346940 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,17497869663694813300 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,1178185768520342099 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,446491489996392359 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 105, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 105, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,8021574905279043171 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,13174311468413708183 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,15880302354919066316 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,5946728594800588900 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 111, 99, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject,9514074055516749235 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,13903913597249585287 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut crate::leanh::LeanObject,16615662997495850524 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,16556904675553485652 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 111, 105, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 105, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,17849391023096305096 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,7054951526961662736 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut crate::leanh::LeanObject,16217565746838389087 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,6890270392074276435 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 99, 111, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,16672968270688273557 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,1439957905510575633 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,36003929318889298 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,14549796982260718866 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 111, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,17569179190824060398 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,11580874657273046830 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,10504416010916204673 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,4596442523591869709 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 111, 111, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,1583659881074599201 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,14083048076001743917 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut crate::leanh::LeanObject,17971250720669795982 as *mut crate::leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut crate::leanh::LeanObject,18033352107593988686 as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_instDecidableEqRcc_decEq___redArg(
    mut v_inst_1399_: *mut crate::leanh::LeanObject,
    mut v_x_1400_: *mut crate::leanh::LeanObject,
    mut v_x_1401_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    v_lower_1402_ = crate::leanh::lean_ctor_get(v_x_1400_, 0);
    crate::leanh::lean_inc(v_lower_1402_);
    v_upper_1403_ = crate::leanh::lean_ctor_get(v_x_1400_, 1);
    crate::leanh::lean_inc(v_upper_1403_);
    crate::leanh::lean_dec_ref(v_x_1400_);
    v_lower_1404_ = crate::leanh::lean_ctor_get(v_x_1401_, 0);
    crate::leanh::lean_inc(v_lower_1404_);
    v_upper_1405_ = crate::leanh::lean_ctor_get(v_x_1401_, 1);
    crate::leanh::lean_inc(v_upper_1405_);
    crate::leanh::lean_dec_ref(v_x_1401_);
    crate::leanh::lean_inc_ref(v_inst_1399_);
    v___x_1406_ = crate::leanh::lean_apply_2(v_inst_1399_, v_lower_1402_, v_lower_1404_);
    v___x_1407_ = (crate::leanh::lean_unbox(v___x_1406_) as u8);
    if v___x_1407_ == 0 {
        let mut v___x_1408_: u8 = 0;
        crate::leanh::lean_dec(v_upper_1405_);
        crate::leanh::lean_dec(v_upper_1403_);
        crate::leanh::lean_dec_ref(v_inst_1399_);
        v___x_1408_ = (crate::leanh::lean_unbox(v___x_1406_) as u8);
        return v___x_1408_;
    } else {
        let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1410_: u8 = 0;
        v___x_1409_ = crate::leanh::lean_apply_2(v_inst_1399_, v_upper_1403_, v_upper_1405_);
        v___x_1410_ = (crate::leanh::lean_unbox(v___x_1409_) as u8);
        return v___x_1410_;
    }
}
pub unsafe fn l_Std_instDecidableEqRcc_decEq___redArg___boxed(
    mut v_inst_1411_: *mut crate::leanh::LeanObject,
    mut v_x_1412_: *mut crate::leanh::LeanObject,
    mut v_x_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1414_: u8 = 0;
    let mut v_r_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1411_, v_x_1412_, v_x_1413_);
    v_r_1415_ = crate::leanh::lean_box((v_res_1414_) as usize);
    return v_r_1415_;
}
pub unsafe fn l_Std_instDecidableEqRcc_decEq(
    mut v_00_u03b1_1416_: *mut crate::leanh::LeanObject,
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
    mut v_x_1418_: *mut crate::leanh::LeanObject,
    mut v_x_1419_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1420_: u8 = 0;
    v___x_1420_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1417_, v_x_1418_, v_x_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Std_instDecidableEqRcc_decEq___boxed(
    mut v_00_u03b1_1421_: *mut crate::leanh::LeanObject,
    mut v_inst_1422_: *mut crate::leanh::LeanObject,
    mut v_x_1423_: *mut crate::leanh::LeanObject,
    mut v_x_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: u8 = 0;
    let mut v_r_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ =
        l_Std_instDecidableEqRcc_decEq(v_00_u03b1_1421_, v_inst_1422_, v_x_1423_, v_x_1424_);
    v_r_1426_ = crate::leanh::lean_box((v_res_1425_) as usize);
    return v_r_1426_;
}
pub unsafe fn l_Std_instDecidableEqRcc___redArg(
    mut v_inst_1427_: *mut crate::leanh::LeanObject,
    mut v_x_1428_: *mut crate::leanh::LeanObject,
    mut v_x_1429_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1430_: u8 = 0;
    v___x_1430_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1427_, v_x_1428_, v_x_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Std_instDecidableEqRcc___redArg___boxed(
    mut v_inst_1431_: *mut crate::leanh::LeanObject,
    mut v_x_1432_: *mut crate::leanh::LeanObject,
    mut v_x_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: u8 = 0;
    let mut v_r_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Std_instDecidableEqRcc___redArg(v_inst_1431_, v_x_1432_, v_x_1433_);
    v_r_1435_ = crate::leanh::lean_box((v_res_1434_) as usize);
    return v_r_1435_;
}
pub unsafe fn l_Std_instDecidableEqRcc(
    mut v_00_u03b1_1436_: *mut crate::leanh::LeanObject,
    mut v_inst_1437_: *mut crate::leanh::LeanObject,
    mut v_x_1438_: *mut crate::leanh::LeanObject,
    mut v_x_1439_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1440_: u8 = 0;
    v___x_1440_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1437_, v_x_1438_, v_x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Std_instDecidableEqRcc___boxed(
    mut v_00_u03b1_1441_: *mut crate::leanh::LeanObject,
    mut v_inst_1442_: *mut crate::leanh::LeanObject,
    mut v_x_1443_: *mut crate::leanh::LeanObject,
    mut v_x_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1445_: u8 = 0;
    let mut v_r_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1445_ = l_Std_instDecidableEqRcc(v_00_u03b1_1441_, v_inst_1442_, v_x_1443_, v_x_1444_);
    v_r_1446_ = crate::leanh::lean_box((v_res_1445_) as usize);
    return v_r_1446_;
}
pub unsafe fn l_Std_instDecidableEqRco_decEq___redArg(
    mut v_inst_1447_: *mut crate::leanh::LeanObject,
    mut v_x_1448_: *mut crate::leanh::LeanObject,
    mut v_x_1449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    v_lower_1450_ = crate::leanh::lean_ctor_get(v_x_1448_, 0);
    crate::leanh::lean_inc(v_lower_1450_);
    v_upper_1451_ = crate::leanh::lean_ctor_get(v_x_1448_, 1);
    crate::leanh::lean_inc(v_upper_1451_);
    crate::leanh::lean_dec_ref(v_x_1448_);
    v_lower_1452_ = crate::leanh::lean_ctor_get(v_x_1449_, 0);
    crate::leanh::lean_inc(v_lower_1452_);
    v_upper_1453_ = crate::leanh::lean_ctor_get(v_x_1449_, 1);
    crate::leanh::lean_inc(v_upper_1453_);
    crate::leanh::lean_dec_ref(v_x_1449_);
    crate::leanh::lean_inc_ref(v_inst_1447_);
    v___x_1454_ = crate::leanh::lean_apply_2(v_inst_1447_, v_lower_1450_, v_lower_1452_);
    v___x_1455_ = (crate::leanh::lean_unbox(v___x_1454_) as u8);
    if v___x_1455_ == 0 {
        let mut v___x_1456_: u8 = 0;
        crate::leanh::lean_dec(v_upper_1453_);
        crate::leanh::lean_dec(v_upper_1451_);
        crate::leanh::lean_dec_ref(v_inst_1447_);
        v___x_1456_ = (crate::leanh::lean_unbox(v___x_1454_) as u8);
        return v___x_1456_;
    } else {
        let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: u8 = 0;
        v___x_1457_ = crate::leanh::lean_apply_2(v_inst_1447_, v_upper_1451_, v_upper_1453_);
        v___x_1458_ = (crate::leanh::lean_unbox(v___x_1457_) as u8);
        return v___x_1458_;
    }
}
pub unsafe fn l_Std_instDecidableEqRco_decEq___redArg___boxed(
    mut v_inst_1459_: *mut crate::leanh::LeanObject,
    mut v_x_1460_: *mut crate::leanh::LeanObject,
    mut v_x_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1462_: u8 = 0;
    let mut v_r_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1459_, v_x_1460_, v_x_1461_);
    v_r_1463_ = crate::leanh::lean_box((v_res_1462_) as usize);
    return v_r_1463_;
}
pub unsafe fn l_Std_instDecidableEqRco_decEq(
    mut v_00_u03b1_1464_: *mut crate::leanh::LeanObject,
    mut v_inst_1465_: *mut crate::leanh::LeanObject,
    mut v_x_1466_: *mut crate::leanh::LeanObject,
    mut v_x_1467_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1468_: u8 = 0;
    v___x_1468_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1465_, v_x_1466_, v_x_1467_);
    return v___x_1468_;
}
pub unsafe fn l_Std_instDecidableEqRco_decEq___boxed(
    mut v_00_u03b1_1469_: *mut crate::leanh::LeanObject,
    mut v_inst_1470_: *mut crate::leanh::LeanObject,
    mut v_x_1471_: *mut crate::leanh::LeanObject,
    mut v_x_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1473_: u8 = 0;
    let mut v_r_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ =
        l_Std_instDecidableEqRco_decEq(v_00_u03b1_1469_, v_inst_1470_, v_x_1471_, v_x_1472_);
    v_r_1474_ = crate::leanh::lean_box((v_res_1473_) as usize);
    return v_r_1474_;
}
pub unsafe fn l_Std_instDecidableEqRco___redArg(
    mut v_inst_1475_: *mut crate::leanh::LeanObject,
    mut v_x_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1478_: u8 = 0;
    v___x_1478_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1475_, v_x_1476_, v_x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Std_instDecidableEqRco___redArg___boxed(
    mut v_inst_1479_: *mut crate::leanh::LeanObject,
    mut v_x_1480_: *mut crate::leanh::LeanObject,
    mut v_x_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1482_: u8 = 0;
    let mut v_r_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Std_instDecidableEqRco___redArg(v_inst_1479_, v_x_1480_, v_x_1481_);
    v_r_1483_ = crate::leanh::lean_box((v_res_1482_) as usize);
    return v_r_1483_;
}
pub unsafe fn l_Std_instDecidableEqRco(
    mut v_00_u03b1_1484_: *mut crate::leanh::LeanObject,
    mut v_inst_1485_: *mut crate::leanh::LeanObject,
    mut v_x_1486_: *mut crate::leanh::LeanObject,
    mut v_x_1487_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1488_: u8 = 0;
    v___x_1488_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1485_, v_x_1486_, v_x_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Std_instDecidableEqRco___boxed(
    mut v_00_u03b1_1489_: *mut crate::leanh::LeanObject,
    mut v_inst_1490_: *mut crate::leanh::LeanObject,
    mut v_x_1491_: *mut crate::leanh::LeanObject,
    mut v_x_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1493_: u8 = 0;
    let mut v_r_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1493_ = l_Std_instDecidableEqRco(v_00_u03b1_1489_, v_inst_1490_, v_x_1491_, v_x_1492_);
    v_r_1494_ = crate::leanh::lean_box((v_res_1493_) as usize);
    return v_r_1494_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq___redArg(
    mut v_inst_1495_: *mut crate::leanh::LeanObject,
    mut v_x_1496_: *mut crate::leanh::LeanObject,
    mut v_x_1497_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    v___x_1498_ = crate::leanh::lean_apply_2(v_inst_1495_, v_x_1496_, v_x_1497_);
    v___x_1499_ = (crate::leanh::lean_unbox(v___x_1498_) as u8);
    return v___x_1499_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq___redArg___boxed(
    mut v_inst_1500_: *mut crate::leanh::LeanObject,
    mut v_x_1501_: *mut crate::leanh::LeanObject,
    mut v_x_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1503_: u8 = 0;
    let mut v_r_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l_Std_instDecidableEqRci_decEq___redArg(v_inst_1500_, v_x_1501_, v_x_1502_);
    v_r_1504_ = crate::leanh::lean_box((v_res_1503_) as usize);
    return v_r_1504_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq(
    mut v_00_u03b1_1505_: *mut crate::leanh::LeanObject,
    mut v_inst_1506_: *mut crate::leanh::LeanObject,
    mut v_x_1507_: *mut crate::leanh::LeanObject,
    mut v_x_1508_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    v___x_1509_ = crate::leanh::lean_apply_2(v_inst_1506_, v_x_1507_, v_x_1508_);
    v___x_1510_ = (crate::leanh::lean_unbox(v___x_1509_) as u8);
    return v___x_1510_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq___boxed(
    mut v_00_u03b1_1511_: *mut crate::leanh::LeanObject,
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
    mut v_x_1513_: *mut crate::leanh::LeanObject,
    mut v_x_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ =
        l_Std_instDecidableEqRci_decEq(v_00_u03b1_1511_, v_inst_1512_, v_x_1513_, v_x_1514_);
    v_r_1516_ = crate::leanh::lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Std_instDecidableEqRci___redArg(
    mut v_inst_1517_: *mut crate::leanh::LeanObject,
    mut v_x_1518_: *mut crate::leanh::LeanObject,
    mut v_x_1519_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    v___x_1520_ = crate::leanh::lean_apply_2(v_inst_1517_, v_x_1518_, v_x_1519_);
    v___x_1521_ = (crate::leanh::lean_unbox(v___x_1520_) as u8);
    return v___x_1521_;
}
pub unsafe fn l_Std_instDecidableEqRci___redArg___boxed(
    mut v_inst_1522_: *mut crate::leanh::LeanObject,
    mut v_x_1523_: *mut crate::leanh::LeanObject,
    mut v_x_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1525_: u8 = 0;
    let mut v_r_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Std_instDecidableEqRci___redArg(v_inst_1522_, v_x_1523_, v_x_1524_);
    v_r_1526_ = crate::leanh::lean_box((v_res_1525_) as usize);
    return v_r_1526_;
}
pub unsafe fn l_Std_instDecidableEqRci(
    mut v_00_u03b1_1527_: *mut crate::leanh::LeanObject,
    mut v_inst_1528_: *mut crate::leanh::LeanObject,
    mut v_x_1529_: *mut crate::leanh::LeanObject,
    mut v_x_1530_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    v___x_1531_ = crate::leanh::lean_apply_2(v_inst_1528_, v_x_1529_, v_x_1530_);
    v___x_1532_ = (crate::leanh::lean_unbox(v___x_1531_) as u8);
    return v___x_1532_;
}
pub unsafe fn l_Std_instDecidableEqRci___boxed(
    mut v_00_u03b1_1533_: *mut crate::leanh::LeanObject,
    mut v_inst_1534_: *mut crate::leanh::LeanObject,
    mut v_x_1535_: *mut crate::leanh::LeanObject,
    mut v_x_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1537_: u8 = 0;
    let mut v_r_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_Std_instDecidableEqRci(v_00_u03b1_1533_, v_inst_1534_, v_x_1535_, v_x_1536_);
    v_r_1538_ = crate::leanh::lean_box((v_res_1537_) as usize);
    return v_r_1538_;
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq___redArg(
    mut v_inst_1539_: *mut crate::leanh::LeanObject,
    mut v_x_1540_: *mut crate::leanh::LeanObject,
    mut v_x_1541_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: u8 = 0;
    v_lower_1542_ = crate::leanh::lean_ctor_get(v_x_1540_, 0);
    crate::leanh::lean_inc(v_lower_1542_);
    v_upper_1543_ = crate::leanh::lean_ctor_get(v_x_1540_, 1);
    crate::leanh::lean_inc(v_upper_1543_);
    crate::leanh::lean_dec_ref(v_x_1540_);
    v_lower_1544_ = crate::leanh::lean_ctor_get(v_x_1541_, 0);
    crate::leanh::lean_inc(v_lower_1544_);
    v_upper_1545_ = crate::leanh::lean_ctor_get(v_x_1541_, 1);
    crate::leanh::lean_inc(v_upper_1545_);
    crate::leanh::lean_dec_ref(v_x_1541_);
    crate::leanh::lean_inc_ref(v_inst_1539_);
    v___x_1546_ = crate::leanh::lean_apply_2(v_inst_1539_, v_lower_1542_, v_lower_1544_);
    v___x_1547_ = (crate::leanh::lean_unbox(v___x_1546_) as u8);
    if v___x_1547_ == 0 {
        let mut v___x_1548_: u8 = 0;
        crate::leanh::lean_dec(v_upper_1545_);
        crate::leanh::lean_dec(v_upper_1543_);
        crate::leanh::lean_dec_ref(v_inst_1539_);
        v___x_1548_ = (crate::leanh::lean_unbox(v___x_1546_) as u8);
        return v___x_1548_;
    } else {
        let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1550_: u8 = 0;
        v___x_1549_ = crate::leanh::lean_apply_2(v_inst_1539_, v_upper_1543_, v_upper_1545_);
        v___x_1550_ = (crate::leanh::lean_unbox(v___x_1549_) as u8);
        return v___x_1550_;
    }
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq___redArg___boxed(
    mut v_inst_1551_: *mut crate::leanh::LeanObject,
    mut v_x_1552_: *mut crate::leanh::LeanObject,
    mut v_x_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1554_: u8 = 0;
    let mut v_r_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1551_, v_x_1552_, v_x_1553_);
    v_r_1555_ = crate::leanh::lean_box((v_res_1554_) as usize);
    return v_r_1555_;
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq(
    mut v_00_u03b1_1556_: *mut crate::leanh::LeanObject,
    mut v_inst_1557_: *mut crate::leanh::LeanObject,
    mut v_x_1558_: *mut crate::leanh::LeanObject,
    mut v_x_1559_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1560_: u8 = 0;
    v___x_1560_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1557_, v_x_1558_, v_x_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq___boxed(
    mut v_00_u03b1_1561_: *mut crate::leanh::LeanObject,
    mut v_inst_1562_: *mut crate::leanh::LeanObject,
    mut v_x_1563_: *mut crate::leanh::LeanObject,
    mut v_x_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1565_: u8 = 0;
    let mut v_r_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1565_ =
        l_Std_instDecidableEqRoc_decEq(v_00_u03b1_1561_, v_inst_1562_, v_x_1563_, v_x_1564_);
    v_r_1566_ = crate::leanh::lean_box((v_res_1565_) as usize);
    return v_r_1566_;
}
pub unsafe fn l_Std_instDecidableEqRoc___redArg(
    mut v_inst_1567_: *mut crate::leanh::LeanObject,
    mut v_x_1568_: *mut crate::leanh::LeanObject,
    mut v_x_1569_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1570_: u8 = 0;
    v___x_1570_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1567_, v_x_1568_, v_x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Std_instDecidableEqRoc___redArg___boxed(
    mut v_inst_1571_: *mut crate::leanh::LeanObject,
    mut v_x_1572_: *mut crate::leanh::LeanObject,
    mut v_x_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: u8 = 0;
    let mut v_r_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_instDecidableEqRoc___redArg(v_inst_1571_, v_x_1572_, v_x_1573_);
    v_r_1575_ = crate::leanh::lean_box((v_res_1574_) as usize);
    return v_r_1575_;
}
pub unsafe fn l_Std_instDecidableEqRoc(
    mut v_00_u03b1_1576_: *mut crate::leanh::LeanObject,
    mut v_inst_1577_: *mut crate::leanh::LeanObject,
    mut v_x_1578_: *mut crate::leanh::LeanObject,
    mut v_x_1579_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1580_: u8 = 0;
    v___x_1580_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1577_, v_x_1578_, v_x_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Std_instDecidableEqRoc___boxed(
    mut v_00_u03b1_1581_: *mut crate::leanh::LeanObject,
    mut v_inst_1582_: *mut crate::leanh::LeanObject,
    mut v_x_1583_: *mut crate::leanh::LeanObject,
    mut v_x_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1585_: u8 = 0;
    let mut v_r_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Std_instDecidableEqRoc(v_00_u03b1_1581_, v_inst_1582_, v_x_1583_, v_x_1584_);
    v_r_1586_ = crate::leanh::lean_box((v_res_1585_) as usize);
    return v_r_1586_;
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq___redArg(
    mut v_inst_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: *mut crate::leanh::LeanObject,
    mut v_x_1589_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    v_lower_1590_ = crate::leanh::lean_ctor_get(v_x_1588_, 0);
    crate::leanh::lean_inc(v_lower_1590_);
    v_upper_1591_ = crate::leanh::lean_ctor_get(v_x_1588_, 1);
    crate::leanh::lean_inc(v_upper_1591_);
    crate::leanh::lean_dec_ref(v_x_1588_);
    v_lower_1592_ = crate::leanh::lean_ctor_get(v_x_1589_, 0);
    crate::leanh::lean_inc(v_lower_1592_);
    v_upper_1593_ = crate::leanh::lean_ctor_get(v_x_1589_, 1);
    crate::leanh::lean_inc(v_upper_1593_);
    crate::leanh::lean_dec_ref(v_x_1589_);
    crate::leanh::lean_inc_ref(v_inst_1587_);
    v___x_1594_ = crate::leanh::lean_apply_2(v_inst_1587_, v_lower_1590_, v_lower_1592_);
    v___x_1595_ = (crate::leanh::lean_unbox(v___x_1594_) as u8);
    if v___x_1595_ == 0 {
        let mut v___x_1596_: u8 = 0;
        crate::leanh::lean_dec(v_upper_1593_);
        crate::leanh::lean_dec(v_upper_1591_);
        crate::leanh::lean_dec_ref(v_inst_1587_);
        v___x_1596_ = (crate::leanh::lean_unbox(v___x_1594_) as u8);
        return v___x_1596_;
    } else {
        let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: u8 = 0;
        v___x_1597_ = crate::leanh::lean_apply_2(v_inst_1587_, v_upper_1591_, v_upper_1593_);
        v___x_1598_ = (crate::leanh::lean_unbox(v___x_1597_) as u8);
        return v___x_1598_;
    }
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq___redArg___boxed(
    mut v_inst_1599_: *mut crate::leanh::LeanObject,
    mut v_x_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1602_: u8 = 0;
    let mut v_r_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1599_, v_x_1600_, v_x_1601_);
    v_r_1603_ = crate::leanh::lean_box((v_res_1602_) as usize);
    return v_r_1603_;
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq(
    mut v_00_u03b1_1604_: *mut crate::leanh::LeanObject,
    mut v_inst_1605_: *mut crate::leanh::LeanObject,
    mut v_x_1606_: *mut crate::leanh::LeanObject,
    mut v_x_1607_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1608_: u8 = 0;
    v___x_1608_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1605_, v_x_1606_, v_x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq___boxed(
    mut v_00_u03b1_1609_: *mut crate::leanh::LeanObject,
    mut v_inst_1610_: *mut crate::leanh::LeanObject,
    mut v_x_1611_: *mut crate::leanh::LeanObject,
    mut v_x_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1613_: u8 = 0;
    let mut v_r_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ =
        l_Std_instDecidableEqRoo_decEq(v_00_u03b1_1609_, v_inst_1610_, v_x_1611_, v_x_1612_);
    v_r_1614_ = crate::leanh::lean_box((v_res_1613_) as usize);
    return v_r_1614_;
}
pub unsafe fn l_Std_instDecidableEqRoo___redArg(
    mut v_inst_1615_: *mut crate::leanh::LeanObject,
    mut v_x_1616_: *mut crate::leanh::LeanObject,
    mut v_x_1617_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1618_: u8 = 0;
    v___x_1618_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1615_, v_x_1616_, v_x_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Std_instDecidableEqRoo___redArg___boxed(
    mut v_inst_1619_: *mut crate::leanh::LeanObject,
    mut v_x_1620_: *mut crate::leanh::LeanObject,
    mut v_x_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1622_: u8 = 0;
    let mut v_r_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Std_instDecidableEqRoo___redArg(v_inst_1619_, v_x_1620_, v_x_1621_);
    v_r_1623_ = crate::leanh::lean_box((v_res_1622_) as usize);
    return v_r_1623_;
}
pub unsafe fn l_Std_instDecidableEqRoo(
    mut v_00_u03b1_1624_: *mut crate::leanh::LeanObject,
    mut v_inst_1625_: *mut crate::leanh::LeanObject,
    mut v_x_1626_: *mut crate::leanh::LeanObject,
    mut v_x_1627_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1628_: u8 = 0;
    v___x_1628_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1625_, v_x_1626_, v_x_1627_);
    return v___x_1628_;
}
pub unsafe fn l_Std_instDecidableEqRoo___boxed(
    mut v_00_u03b1_1629_: *mut crate::leanh::LeanObject,
    mut v_inst_1630_: *mut crate::leanh::LeanObject,
    mut v_x_1631_: *mut crate::leanh::LeanObject,
    mut v_x_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1633_: u8 = 0;
    let mut v_r_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Std_instDecidableEqRoo(v_00_u03b1_1629_, v_inst_1630_, v_x_1631_, v_x_1632_);
    v_r_1634_ = crate::leanh::lean_box((v_res_1633_) as usize);
    return v_r_1634_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq___redArg(
    mut v_inst_1635_: *mut crate::leanh::LeanObject,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
    mut v_x_1637_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    v___x_1638_ = crate::leanh::lean_apply_2(v_inst_1635_, v_x_1636_, v_x_1637_);
    v___x_1639_ = (crate::leanh::lean_unbox(v___x_1638_) as u8);
    return v___x_1639_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq___redArg___boxed(
    mut v_inst_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
    mut v_x_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1643_: u8 = 0;
    let mut v_r_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Std_instDecidableEqRoi_decEq___redArg(v_inst_1640_, v_x_1641_, v_x_1642_);
    v_r_1644_ = crate::leanh::lean_box((v_res_1643_) as usize);
    return v_r_1644_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq(
    mut v_00_u03b1_1645_: *mut crate::leanh::LeanObject,
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_x_1647_: *mut crate::leanh::LeanObject,
    mut v_x_1648_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    v___x_1649_ = crate::leanh::lean_apply_2(v_inst_1646_, v_x_1647_, v_x_1648_);
    v___x_1650_ = (crate::leanh::lean_unbox(v___x_1649_) as u8);
    return v___x_1650_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq___boxed(
    mut v_00_u03b1_1651_: *mut crate::leanh::LeanObject,
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_x_1653_: *mut crate::leanh::LeanObject,
    mut v_x_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ =
        l_Std_instDecidableEqRoi_decEq(v_00_u03b1_1651_, v_inst_1652_, v_x_1653_, v_x_1654_);
    v_r_1656_ = crate::leanh::lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Std_instDecidableEqRoi___redArg(
    mut v_inst_1657_: *mut crate::leanh::LeanObject,
    mut v_x_1658_: *mut crate::leanh::LeanObject,
    mut v_x_1659_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    v___x_1660_ = crate::leanh::lean_apply_2(v_inst_1657_, v_x_1658_, v_x_1659_);
    v___x_1661_ = (crate::leanh::lean_unbox(v___x_1660_) as u8);
    return v___x_1661_;
}
pub unsafe fn l_Std_instDecidableEqRoi___redArg___boxed(
    mut v_inst_1662_: *mut crate::leanh::LeanObject,
    mut v_x_1663_: *mut crate::leanh::LeanObject,
    mut v_x_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1665_: u8 = 0;
    let mut v_r_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Std_instDecidableEqRoi___redArg(v_inst_1662_, v_x_1663_, v_x_1664_);
    v_r_1666_ = crate::leanh::lean_box((v_res_1665_) as usize);
    return v_r_1666_;
}
pub unsafe fn l_Std_instDecidableEqRoi(
    mut v_00_u03b1_1667_: *mut crate::leanh::LeanObject,
    mut v_inst_1668_: *mut crate::leanh::LeanObject,
    mut v_x_1669_: *mut crate::leanh::LeanObject,
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    v___x_1671_ = crate::leanh::lean_apply_2(v_inst_1668_, v_x_1669_, v_x_1670_);
    v___x_1672_ = (crate::leanh::lean_unbox(v___x_1671_) as u8);
    return v___x_1672_;
}
pub unsafe fn l_Std_instDecidableEqRoi___boxed(
    mut v_00_u03b1_1673_: *mut crate::leanh::LeanObject,
    mut v_inst_1674_: *mut crate::leanh::LeanObject,
    mut v_x_1675_: *mut crate::leanh::LeanObject,
    mut v_x_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1677_: u8 = 0;
    let mut v_r_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Std_instDecidableEqRoi(v_00_u03b1_1673_, v_inst_1674_, v_x_1675_, v_x_1676_);
    v_r_1678_ = crate::leanh::lean_box((v_res_1677_) as usize);
    return v_r_1678_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq___redArg(
    mut v_inst_1679_: *mut crate::leanh::LeanObject,
    mut v_x_1680_: *mut crate::leanh::LeanObject,
    mut v_x_1681_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: u8 = 0;
    v___x_1682_ = crate::leanh::lean_apply_2(v_inst_1679_, v_x_1680_, v_x_1681_);
    v___x_1683_ = (crate::leanh::lean_unbox(v___x_1682_) as u8);
    return v___x_1683_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq___redArg___boxed(
    mut v_inst_1684_: *mut crate::leanh::LeanObject,
    mut v_x_1685_: *mut crate::leanh::LeanObject,
    mut v_x_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1687_: u8 = 0;
    let mut v_r_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Std_instDecidableEqRic_decEq___redArg(v_inst_1684_, v_x_1685_, v_x_1686_);
    v_r_1688_ = crate::leanh::lean_box((v_res_1687_) as usize);
    return v_r_1688_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq(
    mut v_00_u03b1_1689_: *mut crate::leanh::LeanObject,
    mut v_inst_1690_: *mut crate::leanh::LeanObject,
    mut v_x_1691_: *mut crate::leanh::LeanObject,
    mut v_x_1692_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    v___x_1693_ = crate::leanh::lean_apply_2(v_inst_1690_, v_x_1691_, v_x_1692_);
    v___x_1694_ = (crate::leanh::lean_unbox(v___x_1693_) as u8);
    return v___x_1694_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq___boxed(
    mut v_00_u03b1_1695_: *mut crate::leanh::LeanObject,
    mut v_inst_1696_: *mut crate::leanh::LeanObject,
    mut v_x_1697_: *mut crate::leanh::LeanObject,
    mut v_x_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1699_: u8 = 0;
    let mut v_r_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ =
        l_Std_instDecidableEqRic_decEq(v_00_u03b1_1695_, v_inst_1696_, v_x_1697_, v_x_1698_);
    v_r_1700_ = crate::leanh::lean_box((v_res_1699_) as usize);
    return v_r_1700_;
}
pub unsafe fn l_Std_instDecidableEqRic___redArg(
    mut v_inst_1701_: *mut crate::leanh::LeanObject,
    mut v_x_1702_: *mut crate::leanh::LeanObject,
    mut v_x_1703_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    v___x_1704_ = crate::leanh::lean_apply_2(v_inst_1701_, v_x_1702_, v_x_1703_);
    v___x_1705_ = (crate::leanh::lean_unbox(v___x_1704_) as u8);
    return v___x_1705_;
}
pub unsafe fn l_Std_instDecidableEqRic___redArg___boxed(
    mut v_inst_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
    mut v_x_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1709_: u8 = 0;
    let mut v_r_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Std_instDecidableEqRic___redArg(v_inst_1706_, v_x_1707_, v_x_1708_);
    v_r_1710_ = crate::leanh::lean_box((v_res_1709_) as usize);
    return v_r_1710_;
}
pub unsafe fn l_Std_instDecidableEqRic(
    mut v_00_u03b1_1711_: *mut crate::leanh::LeanObject,
    mut v_inst_1712_: *mut crate::leanh::LeanObject,
    mut v_x_1713_: *mut crate::leanh::LeanObject,
    mut v_x_1714_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    v___x_1715_ = crate::leanh::lean_apply_2(v_inst_1712_, v_x_1713_, v_x_1714_);
    v___x_1716_ = (crate::leanh::lean_unbox(v___x_1715_) as u8);
    return v___x_1716_;
}
pub unsafe fn l_Std_instDecidableEqRic___boxed(
    mut v_00_u03b1_1717_: *mut crate::leanh::LeanObject,
    mut v_inst_1718_: *mut crate::leanh::LeanObject,
    mut v_x_1719_: *mut crate::leanh::LeanObject,
    mut v_x_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: u8 = 0;
    let mut v_r_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Std_instDecidableEqRic(v_00_u03b1_1717_, v_inst_1718_, v_x_1719_, v_x_1720_);
    v_r_1722_ = crate::leanh::lean_box((v_res_1721_) as usize);
    return v_r_1722_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq___redArg(
    mut v_inst_1723_: *mut crate::leanh::LeanObject,
    mut v_x_1724_: *mut crate::leanh::LeanObject,
    mut v_x_1725_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    v___x_1726_ = crate::leanh::lean_apply_2(v_inst_1723_, v_x_1724_, v_x_1725_);
    v___x_1727_ = (crate::leanh::lean_unbox(v___x_1726_) as u8);
    return v___x_1727_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq___redArg___boxed(
    mut v_inst_1728_: *mut crate::leanh::LeanObject,
    mut v_x_1729_: *mut crate::leanh::LeanObject,
    mut v_x_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1731_: u8 = 0;
    let mut v_r_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Std_instDecidableEqRio_decEq___redArg(v_inst_1728_, v_x_1729_, v_x_1730_);
    v_r_1732_ = crate::leanh::lean_box((v_res_1731_) as usize);
    return v_r_1732_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq(
    mut v_00_u03b1_1733_: *mut crate::leanh::LeanObject,
    mut v_inst_1734_: *mut crate::leanh::LeanObject,
    mut v_x_1735_: *mut crate::leanh::LeanObject,
    mut v_x_1736_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    v___x_1737_ = crate::leanh::lean_apply_2(v_inst_1734_, v_x_1735_, v_x_1736_);
    v___x_1738_ = (crate::leanh::lean_unbox(v___x_1737_) as u8);
    return v___x_1738_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq___boxed(
    mut v_00_u03b1_1739_: *mut crate::leanh::LeanObject,
    mut v_inst_1740_: *mut crate::leanh::LeanObject,
    mut v_x_1741_: *mut crate::leanh::LeanObject,
    mut v_x_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1743_: u8 = 0;
    let mut v_r_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1743_ =
        l_Std_instDecidableEqRio_decEq(v_00_u03b1_1739_, v_inst_1740_, v_x_1741_, v_x_1742_);
    v_r_1744_ = crate::leanh::lean_box((v_res_1743_) as usize);
    return v_r_1744_;
}
pub unsafe fn l_Std_instDecidableEqRio___redArg(
    mut v_inst_1745_: *mut crate::leanh::LeanObject,
    mut v_x_1746_: *mut crate::leanh::LeanObject,
    mut v_x_1747_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    v___x_1748_ = crate::leanh::lean_apply_2(v_inst_1745_, v_x_1746_, v_x_1747_);
    v___x_1749_ = (crate::leanh::lean_unbox(v___x_1748_) as u8);
    return v___x_1749_;
}
pub unsafe fn l_Std_instDecidableEqRio___redArg___boxed(
    mut v_inst_1750_: *mut crate::leanh::LeanObject,
    mut v_x_1751_: *mut crate::leanh::LeanObject,
    mut v_x_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: u8 = 0;
    let mut v_r_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Std_instDecidableEqRio___redArg(v_inst_1750_, v_x_1751_, v_x_1752_);
    v_r_1754_ = crate::leanh::lean_box((v_res_1753_) as usize);
    return v_r_1754_;
}
pub unsafe fn l_Std_instDecidableEqRio(
    mut v_00_u03b1_1755_: *mut crate::leanh::LeanObject,
    mut v_inst_1756_: *mut crate::leanh::LeanObject,
    mut v_x_1757_: *mut crate::leanh::LeanObject,
    mut v_x_1758_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    v___x_1759_ = crate::leanh::lean_apply_2(v_inst_1756_, v_x_1757_, v_x_1758_);
    v___x_1760_ = (crate::leanh::lean_unbox(v___x_1759_) as u8);
    return v___x_1760_;
}
pub unsafe fn l_Std_instDecidableEqRio___boxed(
    mut v_00_u03b1_1761_: *mut crate::leanh::LeanObject,
    mut v_inst_1762_: *mut crate::leanh::LeanObject,
    mut v_x_1763_: *mut crate::leanh::LeanObject,
    mut v_x_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1765_: u8 = 0;
    let mut v_r_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1765_ = l_Std_instDecidableEqRio(v_00_u03b1_1761_, v_inst_1762_, v_x_1763_, v_x_1764_);
    v_r_1766_ = crate::leanh::lean_box((v_res_1765_) as usize);
    return v_r_1766_;
}
pub unsafe fn l_Std_instDecidableEqRii_decEq(
    mut v_00_u03b1_1767_: *mut crate::leanh::LeanObject,
    mut v_inst_1768_: *mut crate::leanh::LeanObject,
    mut v_x_1769_: *mut crate::leanh::LeanObject,
    mut v_x_1770_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1771_: u8 = 0;
    v___x_1771_ = 1;
    return v___x_1771_;
}
pub unsafe fn l_Std_instDecidableEqRii_decEq___boxed(
    mut v_00_u03b1_1772_: *mut crate::leanh::LeanObject,
    mut v_inst_1773_: *mut crate::leanh::LeanObject,
    mut v_x_1774_: *mut crate::leanh::LeanObject,
    mut v_x_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1776_: u8 = 0;
    let mut v_r_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ =
        l_Std_instDecidableEqRii_decEq(v_00_u03b1_1772_, v_inst_1773_, v_x_1774_, v_x_1775_);
    crate::leanh::lean_dec_ref(v_inst_1773_);
    v_r_1777_ = crate::leanh::lean_box((v_res_1776_) as usize);
    return v_r_1777_;
}
pub unsafe fn l_Std_instDecidableEqRii(
    mut v_00_u03b1_1778_: *mut crate::leanh::LeanObject,
    mut v_inst_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
    mut v_x_1781_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1782_: u8 = 0;
    v___x_1782_ = 1;
    return v___x_1782_;
}
pub unsafe fn l_Std_instDecidableEqRii___boxed(
    mut v_00_u03b1_1783_: *mut crate::leanh::LeanObject,
    mut v_inst_1784_: *mut crate::leanh::LeanObject,
    mut v_x_1785_: *mut crate::leanh::LeanObject,
    mut v_x_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1787_: u8 = 0;
    let mut v_r_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1787_ = l_Std_instDecidableEqRii(v_00_u03b1_1783_, v_inst_1784_, v_x_1785_, v_x_1786_);
    crate::leanh::lean_dec_ref(v_inst_1784_);
    v_r_1788_ = crate::leanh::lean_box((v_res_1787_) as usize);
    return v_r_1788_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5;
    v___x_1998_ = l_String_toRawSubstring_x27(v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(
    mut v_x_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    v___x_2025_ = l_Std_term___x2e_x2e_x2e_x3d___00__closed__1;
    crate::leanh::lean_inc(v_x_2022_);
    v___x_2026_ = l_Lean_Syntax_isOfKind(v_x_2022_, v___x_2025_);
    if v___x_2026_ == 0 {
        let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2022_);
        v___x_2027_ = crate::leanh::lean_box(1);
        v___x_2028_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2028_, 0, v___x_2027_);
        crate::leanh::lean_ctor_set(v___x_2028_, 1, v_a_2024_);
        return v___x_2028_;
    } else {
        let mut v_quotContext_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: u8 = 0;
        let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2029_ = crate::leanh::lean_ctor_get(v_a_2023_, 1);
        v_currMacroScope_2030_ = crate::leanh::lean_ctor_get(v_a_2023_, 2);
        v_ref_2031_ = crate::leanh::lean_ctor_get(v_a_2023_, 5);
        v___x_2032_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2033_ = l_Lean_Syntax_getArg(v_x_2022_, v___x_2032_);
        v___x_2034_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2035_ = l_Lean_Syntax_getArg(v_x_2022_, v___x_2034_);
        crate::leanh::lean_dec(v_x_2022_);
        v___x_2036_ = 0;
        v___x_2037_ = l_Lean_SourceInfo_fromRef(v_ref_2031_, v___x_2036_);
        v___x_2038_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6);
        v___x_2040_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9;
        crate::leanh::lean_inc(v_currMacroScope_2030_);
        crate::leanh::lean_inc(v_quotContext_2029_);
        v___x_2041_ =
            l_Lean_addMacroScope(v_quotContext_2029_, v___x_2040_, v_currMacroScope_2030_);
        v___x_2042_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14;
        crate::leanh::lean_inc_n(v___x_2037_, 2);
        v___x_2043_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2037_);
        crate::leanh::lean_ctor_set(v___x_2043_, 1, v___x_2039_);
        crate::leanh::lean_ctor_set(v___x_2043_, 2, v___x_2041_);
        crate::leanh::lean_ctor_set(v___x_2043_, 3, v___x_2042_);
        v___x_2044_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2045_ = l_Lean_Syntax_node2(v___x_2037_, v___x_2044_, v___x_2033_, v___x_2035_);
        v___x_2046_ = l_Lean_Syntax_node2(v___x_2037_, v___x_2038_, v___x_2043_, v___x_2045_);
        v___x_2047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
        crate::leanh::lean_ctor_set(v___x_2047_, 1, v_a_2024_);
        return v___x_2047_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___boxed(
    mut v_x_2048_: *mut crate::leanh::LeanObject,
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(v_x_2048_, v_a_2049_, v_a_2050_);
    crate::leanh::lean_dec_ref(v_a_2049_);
    return v_res_2051_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0;
    v___x_2054_ = l_String_toRawSubstring_x27(v___x_2053_);
    return v___x_2054_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(
    mut v_x_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    v___x_2077_ = l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1;
    crate::leanh::lean_inc(v_x_2074_);
    v___x_2078_ = l_Lean_Syntax_isOfKind(v_x_2074_, v___x_2077_);
    if v___x_2078_ == 0 {
        let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2074_);
        v___x_2079_ = crate::leanh::lean_box(1);
        v___x_2080_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2080_, 0, v___x_2079_);
        crate::leanh::lean_ctor_set(v___x_2080_, 1, v_a_2076_);
        return v___x_2080_;
    } else {
        let mut v_quotContext_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: u8 = 0;
        let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2081_ = crate::leanh::lean_ctor_get(v_a_2075_, 1);
        v_currMacroScope_2082_ = crate::leanh::lean_ctor_get(v_a_2075_, 2);
        v_ref_2083_ = crate::leanh::lean_ctor_get(v_a_2075_, 5);
        v___x_2084_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2085_ = l_Lean_Syntax_getArg(v_x_2074_, v___x_2084_);
        crate::leanh::lean_dec(v_x_2074_);
        v___x_2086_ = 0;
        v___x_2087_ = l_Lean_SourceInfo_fromRef(v_ref_2083_, v___x_2086_);
        v___x_2088_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1);
        v___x_2090_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2082_);
        crate::leanh::lean_inc(v_quotContext_2081_);
        v___x_2091_ =
            l_Lean_addMacroScope(v_quotContext_2081_, v___x_2090_, v_currMacroScope_2082_);
        v___x_2092_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2087_, 2);
        v___x_2093_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2093_, 0, v___x_2087_);
        crate::leanh::lean_ctor_set(v___x_2093_, 1, v___x_2089_);
        crate::leanh::lean_ctor_set(v___x_2093_, 2, v___x_2091_);
        crate::leanh::lean_ctor_set(v___x_2093_, 3, v___x_2092_);
        v___x_2094_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2095_ = l_Lean_Syntax_node1(v___x_2087_, v___x_2094_, v___x_2085_);
        v___x_2096_ = l_Lean_Syntax_node2(v___x_2087_, v___x_2088_, v___x_2093_, v___x_2095_);
        v___x_2097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2097_, 0, v___x_2096_);
        crate::leanh::lean_ctor_set(v___x_2097_, 1, v_a_2076_);
        return v___x_2097_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___boxed(
    mut v_x_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(v_x_2098_, v_a_2099_, v_a_2100_);
    crate::leanh::lean_dec_ref(v_a_2099_);
    return v_res_2101_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2103_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0;
    v___x_2104_ = l_String_toRawSubstring_x27(v___x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(
    mut v_x_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: *mut crate::leanh::LeanObject,
    mut v_a_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    v___x_2127_ = l_Std_term___x2e_x2e_x2e_x2a___closed__2;
    crate::leanh::lean_inc(v_x_2124_);
    v___x_2128_ = l_Lean_Syntax_isOfKind(v_x_2124_, v___x_2127_);
    if v___x_2128_ == 0 {
        let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2124_);
        v___x_2129_ = crate::leanh::lean_box(1);
        v___x_2130_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2130_, 0, v___x_2129_);
        crate::leanh::lean_ctor_set(v___x_2130_, 1, v_a_2126_);
        return v___x_2130_;
    } else {
        let mut v_quotContext_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: u8 = 0;
        let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2131_ = crate::leanh::lean_ctor_get(v_a_2125_, 1);
        v_currMacroScope_2132_ = crate::leanh::lean_ctor_get(v_a_2125_, 2);
        v_ref_2133_ = crate::leanh::lean_ctor_get(v_a_2125_, 5);
        v___x_2134_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2135_ = l_Lean_Syntax_getArg(v_x_2124_, v___x_2134_);
        crate::leanh::lean_dec(v_x_2124_);
        v___x_2136_ = 0;
        v___x_2137_ = l_Lean_SourceInfo_fromRef(v_ref_2133_, v___x_2136_);
        v___x_2138_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2139_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1);
        v___x_2140_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2132_);
        crate::leanh::lean_inc(v_quotContext_2131_);
        v___x_2141_ =
            l_Lean_addMacroScope(v_quotContext_2131_, v___x_2140_, v_currMacroScope_2132_);
        v___x_2142_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8;
        crate::leanh::lean_inc_n(v___x_2137_, 2);
        v___x_2143_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2137_);
        crate::leanh::lean_ctor_set(v___x_2143_, 1, v___x_2139_);
        crate::leanh::lean_ctor_set(v___x_2143_, 2, v___x_2141_);
        crate::leanh::lean_ctor_set(v___x_2143_, 3, v___x_2142_);
        v___x_2144_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2145_ = l_Lean_Syntax_node1(v___x_2137_, v___x_2144_, v___x_2135_);
        v___x_2146_ = l_Lean_Syntax_node2(v___x_2137_, v___x_2138_, v___x_2143_, v___x_2145_);
        v___x_2147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
        crate::leanh::lean_ctor_set(v___x_2147_, 1, v_a_2126_);
        return v___x_2147_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___boxed(
    mut v_x_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(v_x_2148_, v_a_2149_, v_a_2150_);
    crate::leanh::lean_dec_ref(v_a_2149_);
    return v_res_2151_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0;
    v___x_2154_ = l_String_toRawSubstring_x27(v___x_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(
    mut v_x_2174_: *mut crate::leanh::LeanObject,
    mut v_a_2175_: *mut crate::leanh::LeanObject,
    mut v_a_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    v___x_2177_ = l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1;
    v___x_2178_ = l_Lean_Syntax_isOfKind(v_x_2174_, v___x_2177_);
    if v___x_2178_ == 0 {
        let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2179_ = crate::leanh::lean_box(1);
        v___x_2180_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2179_);
        crate::leanh::lean_ctor_set(v___x_2180_, 1, v_a_2176_);
        return v___x_2180_;
    } else {
        let mut v_quotContext_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: u8 = 0;
        let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2181_ = crate::leanh::lean_ctor_get(v_a_2175_, 1);
        v_currMacroScope_2182_ = crate::leanh::lean_ctor_get(v_a_2175_, 2);
        v_ref_2183_ = crate::leanh::lean_ctor_get(v_a_2175_, 5);
        v___x_2184_ = 0;
        v___x_2185_ = l_Lean_SourceInfo_fromRef(v_ref_2183_, v___x_2184_);
        v___x_2186_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1);
        v___x_2187_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2182_);
        crate::leanh::lean_inc(v_quotContext_2181_);
        v___x_2188_ =
            l_Lean_addMacroScope(v_quotContext_2181_, v___x_2187_, v_currMacroScope_2182_);
        v___x_2189_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8;
        v___x_2190_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2190_, 0, v___x_2185_);
        crate::leanh::lean_ctor_set(v___x_2190_, 1, v___x_2186_);
        crate::leanh::lean_ctor_set(v___x_2190_, 2, v___x_2188_);
        crate::leanh::lean_ctor_set(v___x_2190_, 3, v___x_2189_);
        v___x_2191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2190_);
        crate::leanh::lean_ctor_set(v___x_2191_, 1, v_a_2176_);
        return v___x_2191_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___boxed(
    mut v_x_2192_: *mut crate::leanh::LeanObject,
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(v_x_2192_, v_a_2193_, v_a_2194_);
    crate::leanh::lean_dec_ref(v_a_2193_);
    return v_res_2195_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0;
    v___x_2198_ = l_String_toRawSubstring_x27(v___x_2197_);
    return v___x_2198_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(
    mut v_x_2218_: *mut crate::leanh::LeanObject,
    mut v_a_2219_: *mut crate::leanh::LeanObject,
    mut v_a_2220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    v___x_2221_ = l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1;
    crate::leanh::lean_inc(v_x_2218_);
    v___x_2222_ = l_Lean_Syntax_isOfKind(v_x_2218_, v___x_2221_);
    if v___x_2222_ == 0 {
        let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2218_);
        v___x_2223_ = crate::leanh::lean_box(1);
        v___x_2224_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
        crate::leanh::lean_ctor_set(v___x_2224_, 1, v_a_2220_);
        return v___x_2224_;
    } else {
        let mut v_quotContext_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2232_: u8 = 0;
        let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2225_ = crate::leanh::lean_ctor_get(v_a_2219_, 1);
        v_currMacroScope_2226_ = crate::leanh::lean_ctor_get(v_a_2219_, 2);
        v_ref_2227_ = crate::leanh::lean_ctor_get(v_a_2219_, 5);
        v___x_2228_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2229_ = l_Lean_Syntax_getArg(v_x_2218_, v___x_2228_);
        v___x_2230_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2231_ = l_Lean_Syntax_getArg(v_x_2218_, v___x_2230_);
        crate::leanh::lean_dec(v_x_2218_);
        v___x_2232_ = 0;
        v___x_2233_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2232_);
        v___x_2234_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2235_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1);
        v___x_2236_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2226_);
        crate::leanh::lean_inc(v_quotContext_2225_);
        v___x_2237_ =
            l_Lean_addMacroScope(v_quotContext_2225_, v___x_2236_, v_currMacroScope_2226_);
        v___x_2238_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2233_, 2);
        v___x_2239_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2233_);
        crate::leanh::lean_ctor_set(v___x_2239_, 1, v___x_2235_);
        crate::leanh::lean_ctor_set(v___x_2239_, 2, v___x_2237_);
        crate::leanh::lean_ctor_set(v___x_2239_, 3, v___x_2238_);
        v___x_2240_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2241_ = l_Lean_Syntax_node2(v___x_2233_, v___x_2240_, v___x_2229_, v___x_2231_);
        v___x_2242_ = l_Lean_Syntax_node2(v___x_2233_, v___x_2234_, v___x_2239_, v___x_2241_);
        v___x_2243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2243_, 0, v___x_2242_);
        crate::leanh::lean_ctor_set(v___x_2243_, 1, v_a_2220_);
        return v___x_2243_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___boxed(
    mut v_x_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(v_x_2244_, v_a_2245_, v_a_2246_);
    crate::leanh::lean_dec_ref(v_a_2245_);
    return v_res_2247_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0;
    v___x_2250_ = l_String_toRawSubstring_x27(v___x_2249_);
    return v___x_2250_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(
    mut v_x_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_a_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    v___x_2273_ = l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1;
    crate::leanh::lean_inc(v_x_2270_);
    v___x_2274_ = l_Lean_Syntax_isOfKind(v_x_2270_, v___x_2273_);
    if v___x_2274_ == 0 {
        let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2270_);
        v___x_2275_ = crate::leanh::lean_box(1);
        v___x_2276_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
        crate::leanh::lean_ctor_set(v___x_2276_, 1, v_a_2272_);
        return v___x_2276_;
    } else {
        let mut v_quotContext_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: u8 = 0;
        let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2277_ = crate::leanh::lean_ctor_get(v_a_2271_, 1);
        v_currMacroScope_2278_ = crate::leanh::lean_ctor_get(v_a_2271_, 2);
        v_ref_2279_ = crate::leanh::lean_ctor_get(v_a_2271_, 5);
        v___x_2280_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2281_ = l_Lean_Syntax_getArg(v_x_2270_, v___x_2280_);
        crate::leanh::lean_dec(v_x_2270_);
        v___x_2282_ = 0;
        v___x_2283_ = l_Lean_SourceInfo_fromRef(v_ref_2279_, v___x_2282_);
        v___x_2284_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2285_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1);
        v___x_2286_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2278_);
        crate::leanh::lean_inc(v_quotContext_2277_);
        v___x_2287_ =
            l_Lean_addMacroScope(v_quotContext_2277_, v___x_2286_, v_currMacroScope_2278_);
        v___x_2288_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8;
        crate::leanh::lean_inc_n(v___x_2283_, 2);
        v___x_2289_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2283_);
        crate::leanh::lean_ctor_set(v___x_2289_, 1, v___x_2285_);
        crate::leanh::lean_ctor_set(v___x_2289_, 2, v___x_2287_);
        crate::leanh::lean_ctor_set(v___x_2289_, 3, v___x_2288_);
        v___x_2290_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2291_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2290_, v___x_2281_);
        v___x_2292_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2284_, v___x_2289_, v___x_2291_);
        v___x_2293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
        crate::leanh::lean_ctor_set(v___x_2293_, 1, v_a_2272_);
        return v___x_2293_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___boxed(
    mut v_x_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2297_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(v_x_2294_, v_a_2295_, v_a_2296_);
    crate::leanh::lean_dec_ref(v_a_2295_);
    return v_res_2297_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0;
    v___x_2300_ = l_String_toRawSubstring_x27(v___x_2299_);
    return v___x_2300_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(
    mut v_x_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_a_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    v___x_2323_ = l_Std_term___x2e_x2e_x2e_x3c___00__closed__1;
    crate::leanh::lean_inc(v_x_2320_);
    v___x_2324_ = l_Lean_Syntax_isOfKind(v_x_2320_, v___x_2323_);
    if v___x_2324_ == 0 {
        let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2320_);
        v___x_2325_ = crate::leanh::lean_box(1);
        v___x_2326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2326_, 0, v___x_2325_);
        crate::leanh::lean_ctor_set(v___x_2326_, 1, v_a_2322_);
        return v___x_2326_;
    } else {
        let mut v_quotContext_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2327_ = crate::leanh::lean_ctor_get(v_a_2321_, 1);
        v_currMacroScope_2328_ = crate::leanh::lean_ctor_get(v_a_2321_, 2);
        v_ref_2329_ = crate::leanh::lean_ctor_get(v_a_2321_, 5);
        v___x_2330_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2331_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2330_);
        v___x_2332_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2333_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2332_);
        crate::leanh::lean_dec(v_x_2320_);
        v___x_2334_ = 0;
        v___x_2335_ = l_Lean_SourceInfo_fromRef(v_ref_2329_, v___x_2334_);
        v___x_2336_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2337_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2338_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2328_);
        crate::leanh::lean_inc(v_quotContext_2327_);
        v___x_2339_ =
            l_Lean_addMacroScope(v_quotContext_2327_, v___x_2338_, v_currMacroScope_2328_);
        v___x_2340_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2335_, 2);
        v___x_2341_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2335_);
        crate::leanh::lean_ctor_set(v___x_2341_, 1, v___x_2337_);
        crate::leanh::lean_ctor_set(v___x_2341_, 2, v___x_2339_);
        crate::leanh::lean_ctor_set(v___x_2341_, 3, v___x_2340_);
        v___x_2342_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2343_ = l_Lean_Syntax_node2(v___x_2335_, v___x_2342_, v___x_2331_, v___x_2333_);
        v___x_2344_ = l_Lean_Syntax_node2(v___x_2335_, v___x_2336_, v___x_2341_, v___x_2343_);
        v___x_2345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
        crate::leanh::lean_ctor_set(v___x_2345_, 1, v_a_2322_);
        return v___x_2345_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___boxed(
    mut v_x_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v_a_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(v_x_2346_, v_a_2347_, v_a_2348_);
    crate::leanh::lean_dec_ref(v_a_2347_);
    return v_res_2349_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(
    mut v_x_2350_: *mut crate::leanh::LeanObject,
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    v___x_2353_ = l_Std_term___x2e_x2e_x2e___00__closed__1;
    crate::leanh::lean_inc(v_x_2350_);
    v___x_2354_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2353_);
    if v___x_2354_ == 0 {
        let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2350_);
        v___x_2355_ = crate::leanh::lean_box(1);
        v___x_2356_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2356_, 0, v___x_2355_);
        crate::leanh::lean_ctor_set(v___x_2356_, 1, v_a_2352_);
        return v___x_2356_;
    } else {
        let mut v_quotContext_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2364_: u8 = 0;
        let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2357_ = crate::leanh::lean_ctor_get(v_a_2351_, 1);
        v_currMacroScope_2358_ = crate::leanh::lean_ctor_get(v_a_2351_, 2);
        v_ref_2359_ = crate::leanh::lean_ctor_get(v_a_2351_, 5);
        v___x_2360_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2361_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2360_);
        v___x_2362_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2363_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2362_);
        crate::leanh::lean_dec(v_x_2350_);
        v___x_2364_ = 0;
        v___x_2365_ = l_Lean_SourceInfo_fromRef(v_ref_2359_, v___x_2364_);
        v___x_2366_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2367_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2368_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2358_);
        crate::leanh::lean_inc(v_quotContext_2357_);
        v___x_2369_ =
            l_Lean_addMacroScope(v_quotContext_2357_, v___x_2368_, v_currMacroScope_2358_);
        v___x_2370_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2365_, 2);
        v___x_2371_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2371_, 0, v___x_2365_);
        crate::leanh::lean_ctor_set(v___x_2371_, 1, v___x_2367_);
        crate::leanh::lean_ctor_set(v___x_2371_, 2, v___x_2369_);
        crate::leanh::lean_ctor_set(v___x_2371_, 3, v___x_2370_);
        v___x_2372_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2373_ = l_Lean_Syntax_node2(v___x_2365_, v___x_2372_, v___x_2361_, v___x_2363_);
        v___x_2374_ = l_Lean_Syntax_node2(v___x_2365_, v___x_2366_, v___x_2371_, v___x_2373_);
        v___x_2375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2375_, 0, v___x_2374_);
        crate::leanh::lean_ctor_set(v___x_2375_, 1, v_a_2352_);
        return v___x_2375_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1___boxed(
    mut v_x_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
    mut v_a_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(v_x_2376_, v_a_2377_, v_a_2378_);
    crate::leanh::lean_dec_ref(v_a_2377_);
    return v_res_2379_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0;
    v___x_2382_ = l_String_toRawSubstring_x27(v___x_2381_);
    return v___x_2382_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(
    mut v_x_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    v___x_2405_ = l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1;
    crate::leanh::lean_inc(v_x_2402_);
    v___x_2406_ = l_Lean_Syntax_isOfKind(v_x_2402_, v___x_2405_);
    if v___x_2406_ == 0 {
        let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2402_);
        v___x_2407_ = crate::leanh::lean_box(1);
        v___x_2408_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2408_, 0, v___x_2407_);
        crate::leanh::lean_ctor_set(v___x_2408_, 1, v_a_2404_);
        return v___x_2408_;
    } else {
        let mut v_quotContext_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: u8 = 0;
        let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2409_ = crate::leanh::lean_ctor_get(v_a_2403_, 1);
        v_currMacroScope_2410_ = crate::leanh::lean_ctor_get(v_a_2403_, 2);
        v_ref_2411_ = crate::leanh::lean_ctor_get(v_a_2403_, 5);
        v___x_2412_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2413_ = l_Lean_Syntax_getArg(v_x_2402_, v___x_2412_);
        crate::leanh::lean_dec(v_x_2402_);
        v___x_2414_ = 0;
        v___x_2415_ = l_Lean_SourceInfo_fromRef(v_ref_2411_, v___x_2414_);
        v___x_2416_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2417_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2418_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2410_);
        crate::leanh::lean_inc(v_quotContext_2409_);
        v___x_2419_ =
            l_Lean_addMacroScope(v_quotContext_2409_, v___x_2418_, v_currMacroScope_2410_);
        v___x_2420_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2415_, 2);
        v___x_2421_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2415_);
        crate::leanh::lean_ctor_set(v___x_2421_, 1, v___x_2417_);
        crate::leanh::lean_ctor_set(v___x_2421_, 2, v___x_2419_);
        crate::leanh::lean_ctor_set(v___x_2421_, 3, v___x_2420_);
        v___x_2422_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2423_ = l_Lean_Syntax_node1(v___x_2415_, v___x_2422_, v___x_2413_);
        v___x_2424_ = l_Lean_Syntax_node2(v___x_2415_, v___x_2416_, v___x_2421_, v___x_2423_);
        v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
        crate::leanh::lean_ctor_set(v___x_2425_, 1, v_a_2404_);
        return v___x_2425_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___boxed(
    mut v_x_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(v_x_2426_, v_a_2427_, v_a_2428_);
    crate::leanh::lean_dec_ref(v_a_2427_);
    return v_res_2429_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(
    mut v_x_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
    mut v_a_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u8 = 0;
    v___x_2433_ = l_Std_term_x2a_x2e_x2e_x2e___00__closed__1;
    crate::leanh::lean_inc(v_x_2430_);
    v___x_2434_ = l_Lean_Syntax_isOfKind(v_x_2430_, v___x_2433_);
    if v___x_2434_ == 0 {
        let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2430_);
        v___x_2435_ = crate::leanh::lean_box(1);
        v___x_2436_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2436_, 0, v___x_2435_);
        crate::leanh::lean_ctor_set(v___x_2436_, 1, v_a_2432_);
        return v___x_2436_;
    } else {
        let mut v_quotContext_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2442_: u8 = 0;
        let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2437_ = crate::leanh::lean_ctor_get(v_a_2431_, 1);
        v_currMacroScope_2438_ = crate::leanh::lean_ctor_get(v_a_2431_, 2);
        v_ref_2439_ = crate::leanh::lean_ctor_get(v_a_2431_, 5);
        v___x_2440_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2441_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2440_);
        crate::leanh::lean_dec(v_x_2430_);
        v___x_2442_ = 0;
        v___x_2443_ = l_Lean_SourceInfo_fromRef(v_ref_2439_, v___x_2442_);
        v___x_2444_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2445_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2446_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2438_);
        crate::leanh::lean_inc(v_quotContext_2437_);
        v___x_2447_ =
            l_Lean_addMacroScope(v_quotContext_2437_, v___x_2446_, v_currMacroScope_2438_);
        v___x_2448_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2443_, 2);
        v___x_2449_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2449_, 0, v___x_2443_);
        crate::leanh::lean_ctor_set(v___x_2449_, 1, v___x_2445_);
        crate::leanh::lean_ctor_set(v___x_2449_, 2, v___x_2447_);
        crate::leanh::lean_ctor_set(v___x_2449_, 3, v___x_2448_);
        v___x_2450_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2451_ = l_Lean_Syntax_node1(v___x_2443_, v___x_2450_, v___x_2441_);
        v___x_2452_ = l_Lean_Syntax_node2(v___x_2443_, v___x_2444_, v___x_2449_, v___x_2451_);
        v___x_2453_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2453_, 0, v___x_2452_);
        crate::leanh::lean_ctor_set(v___x_2453_, 1, v_a_2432_);
        return v___x_2453_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1___boxed(
    mut v_x_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2457_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(v_x_2454_, v_a_2455_, v_a_2456_);
    crate::leanh::lean_dec_ref(v_a_2455_);
    return v_res_2457_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0;
    v___x_2460_ = l_String_toRawSubstring_x27(v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(
    mut v_x_2480_: *mut crate::leanh::LeanObject,
    mut v_a_2481_: *mut crate::leanh::LeanObject,
    mut v_a_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: u8 = 0;
    v___x_2483_ = l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1;
    crate::leanh::lean_inc(v_x_2480_);
    v___x_2484_ = l_Lean_Syntax_isOfKind(v_x_2480_, v___x_2483_);
    if v___x_2484_ == 0 {
        let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2480_);
        v___x_2485_ = crate::leanh::lean_box(1);
        v___x_2486_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2485_);
        crate::leanh::lean_ctor_set(v___x_2486_, 1, v_a_2482_);
        return v___x_2486_;
    } else {
        let mut v_quotContext_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: u8 = 0;
        let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2487_ = crate::leanh::lean_ctor_get(v_a_2481_, 1);
        v_currMacroScope_2488_ = crate::leanh::lean_ctor_get(v_a_2481_, 2);
        v_ref_2489_ = crate::leanh::lean_ctor_get(v_a_2481_, 5);
        v___x_2490_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2491_ = l_Lean_Syntax_getArg(v_x_2480_, v___x_2490_);
        v___x_2492_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2493_ = l_Lean_Syntax_getArg(v_x_2480_, v___x_2492_);
        crate::leanh::lean_dec(v_x_2480_);
        v___x_2494_ = 0;
        v___x_2495_ = l_Lean_SourceInfo_fromRef(v_ref_2489_, v___x_2494_);
        v___x_2496_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2497_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2498_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2488_);
        crate::leanh::lean_inc(v_quotContext_2487_);
        v___x_2499_ =
            l_Lean_addMacroScope(v_quotContext_2487_, v___x_2498_, v_currMacroScope_2488_);
        v___x_2500_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2495_, 2);
        v___x_2501_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2501_, 0, v___x_2495_);
        crate::leanh::lean_ctor_set(v___x_2501_, 1, v___x_2497_);
        crate::leanh::lean_ctor_set(v___x_2501_, 2, v___x_2499_);
        crate::leanh::lean_ctor_set(v___x_2501_, 3, v___x_2500_);
        v___x_2502_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2503_ = l_Lean_Syntax_node2(v___x_2495_, v___x_2502_, v___x_2491_, v___x_2493_);
        v___x_2504_ = l_Lean_Syntax_node2(v___x_2495_, v___x_2496_, v___x_2501_, v___x_2503_);
        v___x_2505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2505_, 0, v___x_2504_);
        crate::leanh::lean_ctor_set(v___x_2505_, 1, v_a_2482_);
        return v___x_2505_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___boxed(
    mut v_x_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(v_x_2506_, v_a_2507_, v_a_2508_);
    crate::leanh::lean_dec_ref(v_a_2507_);
    return v_res_2509_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(
    mut v_x_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    v___x_2513_ = l_Std_term___x3c_x2e_x2e_x2e___00__closed__1;
    crate::leanh::lean_inc(v_x_2510_);
    v___x_2514_ = l_Lean_Syntax_isOfKind(v_x_2510_, v___x_2513_);
    if v___x_2514_ == 0 {
        let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2510_);
        v___x_2515_ = crate::leanh::lean_box(1);
        v___x_2516_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2516_, 0, v___x_2515_);
        crate::leanh::lean_ctor_set(v___x_2516_, 1, v_a_2512_);
        return v___x_2516_;
    } else {
        let mut v_quotContext_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2524_: u8 = 0;
        let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2517_ = crate::leanh::lean_ctor_get(v_a_2511_, 1);
        v_currMacroScope_2518_ = crate::leanh::lean_ctor_get(v_a_2511_, 2);
        v_ref_2519_ = crate::leanh::lean_ctor_get(v_a_2511_, 5);
        v___x_2520_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2521_ = l_Lean_Syntax_getArg(v_x_2510_, v___x_2520_);
        v___x_2522_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2523_ = l_Lean_Syntax_getArg(v_x_2510_, v___x_2522_);
        crate::leanh::lean_dec(v_x_2510_);
        v___x_2524_ = 0;
        v___x_2525_ = l_Lean_SourceInfo_fromRef(v_ref_2519_, v___x_2524_);
        v___x_2526_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2528_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3;
        crate::leanh::lean_inc(v_currMacroScope_2518_);
        crate::leanh::lean_inc(v_quotContext_2517_);
        v___x_2529_ =
            l_Lean_addMacroScope(v_quotContext_2517_, v___x_2528_, v_currMacroScope_2518_);
        v___x_2530_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8;
        crate::leanh::lean_inc_n(v___x_2525_, 2);
        v___x_2531_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2531_, 0, v___x_2525_);
        crate::leanh::lean_ctor_set(v___x_2531_, 1, v___x_2527_);
        crate::leanh::lean_ctor_set(v___x_2531_, 2, v___x_2529_);
        crate::leanh::lean_ctor_set(v___x_2531_, 3, v___x_2530_);
        v___x_2532_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2533_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2532_, v___x_2521_, v___x_2523_);
        v___x_2534_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2526_, v___x_2531_, v___x_2533_);
        v___x_2535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2534_);
        crate::leanh::lean_ctor_set(v___x_2535_, 1, v_a_2512_);
        return v___x_2535_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1___boxed(
    mut v_x_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(v_x_2536_, v_a_2537_, v_a_2538_);
    crate::leanh::lean_dec_ref(v_a_2537_);
    return v_res_2539_;
}
pub unsafe fn l_Std_Rcc_instMembershipOfLE(
    mut v_00_u03b1_2540_: *mut crate::leanh::LeanObject,
    mut v_inst_2541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = crate::leanh::lean_box(0);
    return v___x_2542_;
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(
    mut v_r_2543_: *mut crate::leanh::LeanObject,
    mut v_a_2544_: *mut crate::leanh::LeanObject,
    mut v_inst_2545_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    v_lower_2546_ = crate::leanh::lean_ctor_get(v_r_2543_, 0);
    crate::leanh::lean_inc(v_lower_2546_);
    v_upper_2547_ = crate::leanh::lean_ctor_get(v_r_2543_, 1);
    crate::leanh::lean_inc(v_upper_2547_);
    crate::leanh::lean_dec_ref(v_r_2543_);
    crate::leanh::lean_inc_ref(v_inst_2545_);
    crate::leanh::lean_inc(v_a_2544_);
    v___x_2548_ = crate::leanh::lean_apply_2(v_inst_2545_, v_lower_2546_, v_a_2544_);
    v___x_2549_ = (crate::leanh::lean_unbox(v___x_2548_) as u8);
    if v___x_2549_ == 0 {
        let mut v___x_2550_: u8 = 0;
        crate::leanh::lean_dec(v_upper_2547_);
        crate::leanh::lean_dec_ref(v_inst_2545_);
        crate::leanh::lean_dec(v_a_2544_);
        v___x_2550_ = (crate::leanh::lean_unbox(v___x_2548_) as u8);
        return v___x_2550_;
    } else {
        let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: u8 = 0;
        v___x_2551_ = crate::leanh::lean_apply_2(v_inst_2545_, v_a_2544_, v_upper_2547_);
        v___x_2552_ = (crate::leanh::lean_unbox(v___x_2551_) as u8);
        return v___x_2552_;
    }
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(
    mut v_r_2553_: *mut crate::leanh::LeanObject,
    mut v_a_2554_: *mut crate::leanh::LeanObject,
    mut v_inst_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2556_: u8 = 0;
    let mut v_r_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ =
        l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_2553_, v_a_2554_, v_inst_2555_);
    v_r_2557_ = crate::leanh::lean_box((v_res_2556_) as usize);
    return v_r_2557_;
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE(
    mut v_00_u03b1_2558_: *mut crate::leanh::LeanObject,
    mut v_r_2559_: *mut crate::leanh::LeanObject,
    mut v_a_2560_: *mut crate::leanh::LeanObject,
    mut v_inst_2561_: *mut crate::leanh::LeanObject,
    mut v_inst_2562_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2563_: u8 = 0;
    v___x_2563_ =
        l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_2559_, v_a_2560_, v_inst_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(
    mut v_00_u03b1_2564_: *mut crate::leanh::LeanObject,
    mut v_r_2565_: *mut crate::leanh::LeanObject,
    mut v_a_2566_: *mut crate::leanh::LeanObject,
    mut v_inst_2567_: *mut crate::leanh::LeanObject,
    mut v_inst_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2569_: u8 = 0;
    let mut v_r_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Std_Rcc_instDecidableMemOfDecidableLE(
        v_00_u03b1_2564_,
        v_r_2565_,
        v_a_2566_,
        v_inst_2567_,
        v_inst_2568_,
    );
    v_r_2570_ = crate::leanh::lean_box((v_res_2569_) as usize);
    return v_r_2570_;
}
pub unsafe fn l_Std_Rco_instMembershipOfLEOfLT(
    mut v_00_u03b1_2571_: *mut crate::leanh::LeanObject,
    mut v_inst_2572_: *mut crate::leanh::LeanObject,
    mut v_inst_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2574_ = crate::leanh::lean_box(0);
    return v___x_2574_;
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
    mut v_r_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
    mut v_inst_2577_: *mut crate::leanh::LeanObject,
    mut v_inst_2578_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: u8 = 0;
    v_lower_2579_ = crate::leanh::lean_ctor_get(v_r_2575_, 0);
    crate::leanh::lean_inc(v_lower_2579_);
    v_upper_2580_ = crate::leanh::lean_ctor_get(v_r_2575_, 1);
    crate::leanh::lean_inc(v_upper_2580_);
    crate::leanh::lean_dec_ref(v_r_2575_);
    crate::leanh::lean_inc(v_a_2576_);
    v___x_2581_ = crate::leanh::lean_apply_2(v_inst_2577_, v_lower_2579_, v_a_2576_);
    v___x_2582_ = (crate::leanh::lean_unbox(v___x_2581_) as u8);
    if v___x_2582_ == 0 {
        let mut v___x_2583_: u8 = 0;
        crate::leanh::lean_dec(v_upper_2580_);
        crate::leanh::lean_dec_ref(v_inst_2578_);
        crate::leanh::lean_dec(v_a_2576_);
        v___x_2583_ = (crate::leanh::lean_unbox(v___x_2581_) as u8);
        return v___x_2583_;
    } else {
        let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2585_: u8 = 0;
        v___x_2584_ = crate::leanh::lean_apply_2(v_inst_2578_, v_a_2576_, v_upper_2580_);
        v___x_2585_ = (crate::leanh::lean_unbox(v___x_2584_) as u8);
        return v___x_2585_;
    }
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(
    mut v_r_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_inst_2588_: *mut crate::leanh::LeanObject,
    mut v_inst_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2590_: u8 = 0;
    let mut v_r_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
        v_r_2586_,
        v_a_2587_,
        v_inst_2588_,
        v_inst_2589_,
    );
    v_r_2591_ = crate::leanh::lean_box((v_res_2590_) as usize);
    return v_r_2591_;
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(
    mut v_00_u03b1_2592_: *mut crate::leanh::LeanObject,
    mut v_r_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_inst_2595_: *mut crate::leanh::LeanObject,
    mut v_inst_2596_: *mut crate::leanh::LeanObject,
    mut v_inst_2597_: *mut crate::leanh::LeanObject,
    mut v_inst_2598_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2599_: u8 = 0;
    v___x_2599_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
        v_r_2593_,
        v_a_2594_,
        v_inst_2596_,
        v_inst_2598_,
    );
    return v___x_2599_;
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(
    mut v_00_u03b1_2600_: *mut crate::leanh::LeanObject,
    mut v_r_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_inst_2603_: *mut crate::leanh::LeanObject,
    mut v_inst_2604_: *mut crate::leanh::LeanObject,
    mut v_inst_2605_: *mut crate::leanh::LeanObject,
    mut v_inst_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2607_: u8 = 0;
    let mut v_r_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(
        v_00_u03b1_2600_,
        v_r_2601_,
        v_a_2602_,
        v_inst_2603_,
        v_inst_2604_,
        v_inst_2605_,
        v_inst_2606_,
    );
    v_r_2608_ = crate::leanh::lean_box((v_res_2607_) as usize);
    return v_r_2608_;
}
pub unsafe fn l_Std_Rci_instMembershipOfLE(
    mut v_00_u03b1_2609_: *mut crate::leanh::LeanObject,
    mut v_inst_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2611_ = crate::leanh::lean_box(0);
    return v___x_2611_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE___redArg(
    mut v_r_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_inst_2614_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: u8 = 0;
    v___x_2615_ = crate::leanh::lean_apply_2(v_inst_2614_, v_r_2612_, v_a_2613_);
    v___x_2616_ = (crate::leanh::lean_unbox(v___x_2615_) as u8);
    return v___x_2616_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(
    mut v_r_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_inst_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ =
        l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_2617_, v_a_2618_, v_inst_2619_);
    v_r_2621_ = crate::leanh::lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE(
    mut v_00_u03b1_2622_: *mut crate::leanh::LeanObject,
    mut v_r_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_inst_2625_: *mut crate::leanh::LeanObject,
    mut v_inst_2626_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    v___x_2627_ = crate::leanh::lean_apply_2(v_inst_2626_, v_r_2623_, v_a_2624_);
    v___x_2628_ = (crate::leanh::lean_unbox(v___x_2627_) as u8);
    return v___x_2628_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE___boxed(
    mut v_00_u03b1_2629_: *mut crate::leanh::LeanObject,
    mut v_r_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_inst_2632_: *mut crate::leanh::LeanObject,
    mut v_inst_2633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2634_: u8 = 0;
    let mut v_r_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2634_ = l_Std_Rci_instDecidableMemOfDecidableLE(
        v_00_u03b1_2629_,
        v_r_2630_,
        v_a_2631_,
        v_inst_2632_,
        v_inst_2633_,
    );
    v_r_2635_ = crate::leanh::lean_box((v_res_2634_) as usize);
    return v_r_2635_;
}
pub unsafe fn l_Std_Roc_instMembershipOfLEOfLT(
    mut v_00_u03b1_2636_: *mut crate::leanh::LeanObject,
    mut v_inst_2637_: *mut crate::leanh::LeanObject,
    mut v_inst_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = crate::leanh::lean_box(0);
    return v___x_2639_;
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
    mut v_r_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_inst_2642_: *mut crate::leanh::LeanObject,
    mut v_inst_2643_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    v_lower_2644_ = crate::leanh::lean_ctor_get(v_r_2640_, 0);
    crate::leanh::lean_inc(v_lower_2644_);
    v_upper_2645_ = crate::leanh::lean_ctor_get(v_r_2640_, 1);
    crate::leanh::lean_inc(v_upper_2645_);
    crate::leanh::lean_dec_ref(v_r_2640_);
    crate::leanh::lean_inc(v_a_2641_);
    v___x_2646_ = crate::leanh::lean_apply_2(v_inst_2643_, v_lower_2644_, v_a_2641_);
    v___x_2647_ = (crate::leanh::lean_unbox(v___x_2646_) as u8);
    if v___x_2647_ == 0 {
        let mut v___x_2648_: u8 = 0;
        crate::leanh::lean_dec(v_upper_2645_);
        crate::leanh::lean_dec_ref(v_inst_2642_);
        crate::leanh::lean_dec(v_a_2641_);
        v___x_2648_ = (crate::leanh::lean_unbox(v___x_2646_) as u8);
        return v___x_2648_;
    } else {
        let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2650_: u8 = 0;
        v___x_2649_ = crate::leanh::lean_apply_2(v_inst_2642_, v_a_2641_, v_upper_2645_);
        v___x_2650_ = (crate::leanh::lean_unbox(v___x_2649_) as u8);
        return v___x_2650_;
    }
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(
    mut v_r_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_inst_2653_: *mut crate::leanh::LeanObject,
    mut v_inst_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2655_: u8 = 0;
    let mut v_r_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
        v_r_2651_,
        v_a_2652_,
        v_inst_2653_,
        v_inst_2654_,
    );
    v_r_2656_ = crate::leanh::lean_box((v_res_2655_) as usize);
    return v_r_2656_;
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(
    mut v_00_u03b1_2657_: *mut crate::leanh::LeanObject,
    mut v_r_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_inst_2660_: *mut crate::leanh::LeanObject,
    mut v_inst_2661_: *mut crate::leanh::LeanObject,
    mut v_inst_2662_: *mut crate::leanh::LeanObject,
    mut v_inst_2663_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2664_: u8 = 0;
    v___x_2664_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
        v_r_2658_,
        v_a_2659_,
        v_inst_2661_,
        v_inst_2663_,
    );
    return v___x_2664_;
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(
    mut v_00_u03b1_2665_: *mut crate::leanh::LeanObject,
    mut v_r_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_inst_2668_: *mut crate::leanh::LeanObject,
    mut v_inst_2669_: *mut crate::leanh::LeanObject,
    mut v_inst_2670_: *mut crate::leanh::LeanObject,
    mut v_inst_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: u8 = 0;
    let mut v_r_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(
        v_00_u03b1_2665_,
        v_r_2666_,
        v_a_2667_,
        v_inst_2668_,
        v_inst_2669_,
        v_inst_2670_,
        v_inst_2671_,
    );
    v_r_2673_ = crate::leanh::lean_box((v_res_2672_) as usize);
    return v_r_2673_;
}
pub unsafe fn l_Std_Roo_instMembershipOfLT(
    mut v_00_u03b1_2674_: *mut crate::leanh::LeanObject,
    mut v_inst_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = crate::leanh::lean_box(0);
    return v___x_2676_;
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT___redArg(
    mut v_r_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_inst_2679_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lower_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    v_lower_2680_ = crate::leanh::lean_ctor_get(v_r_2677_, 0);
    crate::leanh::lean_inc(v_lower_2680_);
    v_upper_2681_ = crate::leanh::lean_ctor_get(v_r_2677_, 1);
    crate::leanh::lean_inc(v_upper_2681_);
    crate::leanh::lean_dec_ref(v_r_2677_);
    crate::leanh::lean_inc_ref(v_inst_2679_);
    crate::leanh::lean_inc(v_a_2678_);
    v___x_2682_ = crate::leanh::lean_apply_2(v_inst_2679_, v_lower_2680_, v_a_2678_);
    v___x_2683_ = (crate::leanh::lean_unbox(v___x_2682_) as u8);
    if v___x_2683_ == 0 {
        let mut v___x_2684_: u8 = 0;
        crate::leanh::lean_dec(v_upper_2681_);
        crate::leanh::lean_dec_ref(v_inst_2679_);
        crate::leanh::lean_dec(v_a_2678_);
        v___x_2684_ = (crate::leanh::lean_unbox(v___x_2682_) as u8);
        return v___x_2684_;
    } else {
        let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: u8 = 0;
        v___x_2685_ = crate::leanh::lean_apply_2(v_inst_2679_, v_a_2678_, v_upper_2681_);
        v___x_2686_ = (crate::leanh::lean_unbox(v___x_2685_) as u8);
        return v___x_2686_;
    }
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(
    mut v_r_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_inst_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2690_: u8 = 0;
    let mut v_r_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ =
        l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_2687_, v_a_2688_, v_inst_2689_);
    v_r_2691_ = crate::leanh::lean_box((v_res_2690_) as usize);
    return v_r_2691_;
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT(
    mut v_00_u03b1_2692_: *mut crate::leanh::LeanObject,
    mut v_r_2693_: *mut crate::leanh::LeanObject,
    mut v_a_2694_: *mut crate::leanh::LeanObject,
    mut v_inst_2695_: *mut crate::leanh::LeanObject,
    mut v_inst_2696_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2697_: u8 = 0;
    v___x_2697_ =
        l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_2693_, v_a_2694_, v_inst_2696_);
    return v___x_2697_;
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT___boxed(
    mut v_00_u03b1_2698_: *mut crate::leanh::LeanObject,
    mut v_r_2699_: *mut crate::leanh::LeanObject,
    mut v_a_2700_: *mut crate::leanh::LeanObject,
    mut v_inst_2701_: *mut crate::leanh::LeanObject,
    mut v_inst_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2703_: u8 = 0;
    let mut v_r_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Std_Roo_instDecidableMemOfDecidableLT(
        v_00_u03b1_2698_,
        v_r_2699_,
        v_a_2700_,
        v_inst_2701_,
        v_inst_2702_,
    );
    v_r_2704_ = crate::leanh::lean_box((v_res_2703_) as usize);
    return v_r_2704_;
}
pub unsafe fn l_Std_Roi_instMembershipOfLT(
    mut v_00_u03b1_2705_: *mut crate::leanh::LeanObject,
    mut v_inst_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = crate::leanh::lean_box(0);
    return v___x_2707_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT___redArg(
    mut v_r_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_inst_2710_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    v___x_2711_ = crate::leanh::lean_apply_2(v_inst_2710_, v_r_2708_, v_a_2709_);
    v___x_2712_ = (crate::leanh::lean_unbox(v___x_2711_) as u8);
    return v___x_2712_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(
    mut v_r_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_inst_2715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2716_: u8 = 0;
    let mut v_r_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2716_ =
        l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_2713_, v_a_2714_, v_inst_2715_);
    v_r_2717_ = crate::leanh::lean_box((v_res_2716_) as usize);
    return v_r_2717_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT(
    mut v_00_u03b1_2718_: *mut crate::leanh::LeanObject,
    mut v_r_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_inst_2721_: *mut crate::leanh::LeanObject,
    mut v_inst_2722_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: u8 = 0;
    v___x_2723_ = crate::leanh::lean_apply_2(v_inst_2722_, v_r_2719_, v_a_2720_);
    v___x_2724_ = (crate::leanh::lean_unbox(v___x_2723_) as u8);
    return v___x_2724_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT___boxed(
    mut v_00_u03b1_2725_: *mut crate::leanh::LeanObject,
    mut v_r_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_inst_2728_: *mut crate::leanh::LeanObject,
    mut v_inst_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2730_: u8 = 0;
    let mut v_r_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l_Std_Roi_instDecidableMemOfDecidableLT(
        v_00_u03b1_2725_,
        v_r_2726_,
        v_a_2727_,
        v_inst_2728_,
        v_inst_2729_,
    );
    v_r_2731_ = crate::leanh::lean_box((v_res_2730_) as usize);
    return v_r_2731_;
}
pub unsafe fn l_Std_Ric_instMembershipOfLE(
    mut v_00_u03b1_2732_: *mut crate::leanh::LeanObject,
    mut v_inst_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = crate::leanh::lean_box(0);
    return v___x_2734_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE___redArg(
    mut v_r_2735_: *mut crate::leanh::LeanObject,
    mut v_a_2736_: *mut crate::leanh::LeanObject,
    mut v_inst_2737_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    v___x_2738_ = crate::leanh::lean_apply_2(v_inst_2737_, v_a_2736_, v_r_2735_);
    v___x_2739_ = (crate::leanh::lean_unbox(v___x_2738_) as u8);
    return v___x_2739_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(
    mut v_r_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_inst_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2743_: u8 = 0;
    let mut v_r_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2743_ =
        l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_2740_, v_a_2741_, v_inst_2742_);
    v_r_2744_ = crate::leanh::lean_box((v_res_2743_) as usize);
    return v_r_2744_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE(
    mut v_00_u03b1_2745_: *mut crate::leanh::LeanObject,
    mut v_r_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
    mut v_inst_2748_: *mut crate::leanh::LeanObject,
    mut v_inst_2749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    v___x_2750_ = crate::leanh::lean_apply_2(v_inst_2749_, v_a_2747_, v_r_2746_);
    v___x_2751_ = (crate::leanh::lean_unbox(v___x_2750_) as u8);
    return v___x_2751_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE___boxed(
    mut v_00_u03b1_2752_: *mut crate::leanh::LeanObject,
    mut v_r_2753_: *mut crate::leanh::LeanObject,
    mut v_a_2754_: *mut crate::leanh::LeanObject,
    mut v_inst_2755_: *mut crate::leanh::LeanObject,
    mut v_inst_2756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2757_: u8 = 0;
    let mut v_r_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2757_ = l_Std_Ric_instDecidableMemOfDecidableLE(
        v_00_u03b1_2752_,
        v_r_2753_,
        v_a_2754_,
        v_inst_2755_,
        v_inst_2756_,
    );
    v_r_2758_ = crate::leanh::lean_box((v_res_2757_) as usize);
    return v_r_2758_;
}
pub unsafe fn l_Std_Rio_instMembershipOfLT(
    mut v_00_u03b1_2759_: *mut crate::leanh::LeanObject,
    mut v_inst_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = crate::leanh::lean_box(0);
    return v___x_2761_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT___redArg(
    mut v_r_2762_: *mut crate::leanh::LeanObject,
    mut v_a_2763_: *mut crate::leanh::LeanObject,
    mut v_inst_2764_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    v___x_2765_ = crate::leanh::lean_apply_2(v_inst_2764_, v_a_2763_, v_r_2762_);
    v___x_2766_ = (crate::leanh::lean_unbox(v___x_2765_) as u8);
    return v___x_2766_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(
    mut v_r_2767_: *mut crate::leanh::LeanObject,
    mut v_a_2768_: *mut crate::leanh::LeanObject,
    mut v_inst_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2770_: u8 = 0;
    let mut v_r_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2770_ =
        l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_2767_, v_a_2768_, v_inst_2769_);
    v_r_2771_ = crate::leanh::lean_box((v_res_2770_) as usize);
    return v_r_2771_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT(
    mut v_00_u03b1_2772_: *mut crate::leanh::LeanObject,
    mut v_r_2773_: *mut crate::leanh::LeanObject,
    mut v_a_2774_: *mut crate::leanh::LeanObject,
    mut v_inst_2775_: *mut crate::leanh::LeanObject,
    mut v_inst_2776_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    v___x_2777_ = crate::leanh::lean_apply_2(v_inst_2776_, v_a_2774_, v_r_2773_);
    v___x_2778_ = (crate::leanh::lean_unbox(v___x_2777_) as u8);
    return v___x_2778_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT___boxed(
    mut v_00_u03b1_2779_: *mut crate::leanh::LeanObject,
    mut v_r_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_inst_2782_: *mut crate::leanh::LeanObject,
    mut v_inst_2783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2784_: u8 = 0;
    let mut v_r_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2784_ = l_Std_Rio_instDecidableMemOfDecidableLT(
        v_00_u03b1_2779_,
        v_r_2780_,
        v_a_2781_,
        v_inst_2782_,
        v_inst_2783_,
    );
    v_r_2785_ = crate::leanh::lean_box((v_res_2784_) as usize);
    return v_r_2785_;
}
pub unsafe fn l_Std_Rii_instMembership(
    mut v_00_u03b1_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = crate::leanh::lean_box(0);
    return v___x_2787_;
}
pub unsafe fn l_Std_Rii_instDecidableMem(
    mut v_00_u03b1_2788_: *mut crate::leanh::LeanObject,
    mut v_r_2789_: *mut crate::leanh::LeanObject,
    mut v_a_2790_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2791_: u8 = 0;
    v___x_2791_ = 1;
    return v___x_2791_;
}
pub unsafe fn l_Std_Rii_instDecidableMem___boxed(
    mut v_00_u03b1_2792_: *mut crate::leanh::LeanObject,
    mut v_r_2793_: *mut crate::leanh::LeanObject,
    mut v_a_2794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2795_: u8 = 0;
    let mut v_r_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2795_ = l_Std_Rii_instDecidableMem(v_00_u03b1_2792_, v_r_2793_, v_a_2794_);
    crate::leanh::lean_dec(v_a_2794_);
    v_r_2796_ = crate::leanh::lean_box((v_res_2795_) as usize);
    return v_r_2796_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_PRange(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_PRange(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_PRange(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_PRange(builtin);
}
