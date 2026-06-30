// Lean compiler output
// Module: Init.Data.Range.Polymorphic.PRange
// Imports: Init.Data.Range.Polymorphic.UpwardEnumerable
use crate::r#gen::Init::Data::Range::Polymorphic::UpwardEnumerable::{
    initialize_Init_Data_Range_Polymorphic_UpwardEnumerable,
    runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__1_value)
        as *mut leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e_x2a___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__1_value)
                as *mut leanh::LeanObject,
            12901981646182791257 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__3_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x2a___closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__2_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x2a___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e_x2a: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15812821569646102790 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e_x2a: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            18313290646982499243 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e_x2a: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value)
                as *mut leanh::LeanObject,
            4456104206502475912 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3c___00__closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e_x3c__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__0_value)
                as *mut leanh::LeanObject,
            5394156637022377744 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__2_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value)
                as *mut leanh::LeanObject,
            17665753292882927436 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e_x3c__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value)
                as *mut leanh::LeanObject,
            10703712094186559148 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value)
                as *mut leanh::LeanObject,
            17893611459657078921 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e_x3c__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value)
                as *mut leanh::LeanObject,
            3473794126537410698 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value)
                as *mut leanh::LeanObject,
            8312988086032421140 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x2e_x2e_x2e_x3d___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x2e_x2e_x2e_x3d__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value)
                as *mut leanh::LeanObject,
            897828399751270016 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term_x2a_x2e_x2e_x2e_x3d__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value)
                as *mut leanh::LeanObject,
            15212140180363167796 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 4,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_term___x3c_x2e_x2e_x2e_x3d__: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 99, 99, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject,16265292064117835183 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,8855140571667196803 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject,16437420457889295896 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,15874481382248158464 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 99, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject,16004387948037561718 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,7181152285640718342 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject,8649810267064386489 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,8380740754681987765 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 99, 105, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 105, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,6989692408478346940 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,17497869663694813300 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,1178185768520342099 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,446491489996392359 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 105, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 105, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,8021574905279043171 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,13174311468413708183 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,15880302354919066316 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,5946728594800588900 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 111, 99, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 99, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject,9514074055516749235 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,13903913597249585287 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value) as *mut leanh::LeanObject,16615662997495850524 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,16556904675553485652 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 111, 105, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 105, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,17849391023096305096 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,7054951526961662736 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value) as *mut leanh::LeanObject,16217565746838389087 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,6890270392074276435 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 99, 111, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 99, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject,16672968270688273557 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,1439957905510575633 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject,36003929318889298 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,14549796982260718866 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 111, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 105, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject,17569179190824060398 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,11580874657273046830 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject,10504416010916204673 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,4596442523591869709 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 111, 111, 46, 109, 107, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 111, 111, 0]};
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject,1583659881074599201 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,14083048076001743917 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value) as *mut leanh::LeanObject;
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_term___x2e_x2e_x2e_x2a___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value) as *mut leanh::LeanObject,17971250720669795982 as *mut leanh::LeanObject] };
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value) as *mut leanh::LeanObject,18033352107593988686 as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_instDecidableEqRcc_decEq___redArg(
    mut v_inst_1399_: *mut leanh::LeanObject,
    mut v_x_1400_: *mut leanh::LeanObject,
    mut v_x_1401_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    v_lower_1402_ = leanh::lean_ctor_get(v_x_1400_, 0);
    leanh::lean_inc(v_lower_1402_);
    v_upper_1403_ = leanh::lean_ctor_get(v_x_1400_, 1);
    leanh::lean_inc(v_upper_1403_);
    leanh::lean_dec_ref(v_x_1400_);
    v_lower_1404_ = leanh::lean_ctor_get(v_x_1401_, 0);
    leanh::lean_inc(v_lower_1404_);
    v_upper_1405_ = leanh::lean_ctor_get(v_x_1401_, 1);
    leanh::lean_inc(v_upper_1405_);
    leanh::lean_dec_ref(v_x_1401_);
    leanh::lean_inc_ref(v_inst_1399_);
    v___x_1406_ = leanh::lean_apply_2(v_inst_1399_, v_lower_1402_, v_lower_1404_);
    v___x_1407_ = (leanh::lean_unbox(v___x_1406_) as u8);
    if v___x_1407_ == 0 {
        let mut v___x_1408_: u8 = 0;
        leanh::lean_dec(v_upper_1405_);
        leanh::lean_dec(v_upper_1403_);
        leanh::lean_dec_ref(v_inst_1399_);
        v___x_1408_ = (leanh::lean_unbox(v___x_1406_) as u8);
        return v___x_1408_;
    } else {
        let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1410_: u8 = 0;
        v___x_1409_ = leanh::lean_apply_2(v_inst_1399_, v_upper_1403_, v_upper_1405_);
        v___x_1410_ = (leanh::lean_unbox(v___x_1409_) as u8);
        return v___x_1410_;
    }
}
pub unsafe fn l_Std_instDecidableEqRcc_decEq___redArg___boxed(
    mut v_inst_1411_: *mut leanh::LeanObject,
    mut v_x_1412_: *mut leanh::LeanObject,
    mut v_x_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1414_: u8 = 0;
    let mut v_r_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1411_, v_x_1412_, v_x_1413_);
    v_r_1415_ = leanh::lean_box((v_res_1414_) as usize);
    return v_r_1415_;
}
pub unsafe fn l_Std_instDecidableEqRcc_decEq(
    mut v_00_u03b1_1416_: *mut leanh::LeanObject,
    mut v_inst_1417_: *mut leanh::LeanObject,
    mut v_x_1418_: *mut leanh::LeanObject,
    mut v_x_1419_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1420_: u8 = 0;
    v___x_1420_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1417_, v_x_1418_, v_x_1419_);
    return v___x_1420_;
}
pub unsafe fn l_Std_instDecidableEqRcc_decEq___boxed(
    mut v_00_u03b1_1421_: *mut leanh::LeanObject,
    mut v_inst_1422_: *mut leanh::LeanObject,
    mut v_x_1423_: *mut leanh::LeanObject,
    mut v_x_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1425_: u8 = 0;
    let mut v_r_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ =
        l_Std_instDecidableEqRcc_decEq(v_00_u03b1_1421_, v_inst_1422_, v_x_1423_, v_x_1424_);
    v_r_1426_ = leanh::lean_box((v_res_1425_) as usize);
    return v_r_1426_;
}
pub unsafe fn l_Std_instDecidableEqRcc___redArg(
    mut v_inst_1427_: *mut leanh::LeanObject,
    mut v_x_1428_: *mut leanh::LeanObject,
    mut v_x_1429_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1430_: u8 = 0;
    v___x_1430_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1427_, v_x_1428_, v_x_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Std_instDecidableEqRcc___redArg___boxed(
    mut v_inst_1431_: *mut leanh::LeanObject,
    mut v_x_1432_: *mut leanh::LeanObject,
    mut v_x_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1434_: u8 = 0;
    let mut v_r_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Std_instDecidableEqRcc___redArg(v_inst_1431_, v_x_1432_, v_x_1433_);
    v_r_1435_ = leanh::lean_box((v_res_1434_) as usize);
    return v_r_1435_;
}
pub unsafe fn l_Std_instDecidableEqRcc(
    mut v_00_u03b1_1436_: *mut leanh::LeanObject,
    mut v_inst_1437_: *mut leanh::LeanObject,
    mut v_x_1438_: *mut leanh::LeanObject,
    mut v_x_1439_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1440_: u8 = 0;
    v___x_1440_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1437_, v_x_1438_, v_x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Std_instDecidableEqRcc___boxed(
    mut v_00_u03b1_1441_: *mut leanh::LeanObject,
    mut v_inst_1442_: *mut leanh::LeanObject,
    mut v_x_1443_: *mut leanh::LeanObject,
    mut v_x_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1445_: u8 = 0;
    let mut v_r_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1445_ = l_Std_instDecidableEqRcc(v_00_u03b1_1441_, v_inst_1442_, v_x_1443_, v_x_1444_);
    v_r_1446_ = leanh::lean_box((v_res_1445_) as usize);
    return v_r_1446_;
}
pub unsafe fn l_Std_instDecidableEqRco_decEq___redArg(
    mut v_inst_1447_: *mut leanh::LeanObject,
    mut v_x_1448_: *mut leanh::LeanObject,
    mut v_x_1449_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    v_lower_1450_ = leanh::lean_ctor_get(v_x_1448_, 0);
    leanh::lean_inc(v_lower_1450_);
    v_upper_1451_ = leanh::lean_ctor_get(v_x_1448_, 1);
    leanh::lean_inc(v_upper_1451_);
    leanh::lean_dec_ref(v_x_1448_);
    v_lower_1452_ = leanh::lean_ctor_get(v_x_1449_, 0);
    leanh::lean_inc(v_lower_1452_);
    v_upper_1453_ = leanh::lean_ctor_get(v_x_1449_, 1);
    leanh::lean_inc(v_upper_1453_);
    leanh::lean_dec_ref(v_x_1449_);
    leanh::lean_inc_ref(v_inst_1447_);
    v___x_1454_ = leanh::lean_apply_2(v_inst_1447_, v_lower_1450_, v_lower_1452_);
    v___x_1455_ = (leanh::lean_unbox(v___x_1454_) as u8);
    if v___x_1455_ == 0 {
        let mut v___x_1456_: u8 = 0;
        leanh::lean_dec(v_upper_1453_);
        leanh::lean_dec(v_upper_1451_);
        leanh::lean_dec_ref(v_inst_1447_);
        v___x_1456_ = (leanh::lean_unbox(v___x_1454_) as u8);
        return v___x_1456_;
    } else {
        let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1458_: u8 = 0;
        v___x_1457_ = leanh::lean_apply_2(v_inst_1447_, v_upper_1451_, v_upper_1453_);
        v___x_1458_ = (leanh::lean_unbox(v___x_1457_) as u8);
        return v___x_1458_;
    }
}
pub unsafe fn l_Std_instDecidableEqRco_decEq___redArg___boxed(
    mut v_inst_1459_: *mut leanh::LeanObject,
    mut v_x_1460_: *mut leanh::LeanObject,
    mut v_x_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1462_: u8 = 0;
    let mut v_r_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1459_, v_x_1460_, v_x_1461_);
    v_r_1463_ = leanh::lean_box((v_res_1462_) as usize);
    return v_r_1463_;
}
pub unsafe fn l_Std_instDecidableEqRco_decEq(
    mut v_00_u03b1_1464_: *mut leanh::LeanObject,
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_x_1466_: *mut leanh::LeanObject,
    mut v_x_1467_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1468_: u8 = 0;
    v___x_1468_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1465_, v_x_1466_, v_x_1467_);
    return v___x_1468_;
}
pub unsafe fn l_Std_instDecidableEqRco_decEq___boxed(
    mut v_00_u03b1_1469_: *mut leanh::LeanObject,
    mut v_inst_1470_: *mut leanh::LeanObject,
    mut v_x_1471_: *mut leanh::LeanObject,
    mut v_x_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1473_: u8 = 0;
    let mut v_r_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ =
        l_Std_instDecidableEqRco_decEq(v_00_u03b1_1469_, v_inst_1470_, v_x_1471_, v_x_1472_);
    v_r_1474_ = leanh::lean_box((v_res_1473_) as usize);
    return v_r_1474_;
}
pub unsafe fn l_Std_instDecidableEqRco___redArg(
    mut v_inst_1475_: *mut leanh::LeanObject,
    mut v_x_1476_: *mut leanh::LeanObject,
    mut v_x_1477_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1478_: u8 = 0;
    v___x_1478_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1475_, v_x_1476_, v_x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Std_instDecidableEqRco___redArg___boxed(
    mut v_inst_1479_: *mut leanh::LeanObject,
    mut v_x_1480_: *mut leanh::LeanObject,
    mut v_x_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1482_: u8 = 0;
    let mut v_r_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Std_instDecidableEqRco___redArg(v_inst_1479_, v_x_1480_, v_x_1481_);
    v_r_1483_ = leanh::lean_box((v_res_1482_) as usize);
    return v_r_1483_;
}
pub unsafe fn l_Std_instDecidableEqRco(
    mut v_00_u03b1_1484_: *mut leanh::LeanObject,
    mut v_inst_1485_: *mut leanh::LeanObject,
    mut v_x_1486_: *mut leanh::LeanObject,
    mut v_x_1487_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1488_: u8 = 0;
    v___x_1488_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_1485_, v_x_1486_, v_x_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Std_instDecidableEqRco___boxed(
    mut v_00_u03b1_1489_: *mut leanh::LeanObject,
    mut v_inst_1490_: *mut leanh::LeanObject,
    mut v_x_1491_: *mut leanh::LeanObject,
    mut v_x_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1493_: u8 = 0;
    let mut v_r_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1493_ = l_Std_instDecidableEqRco(v_00_u03b1_1489_, v_inst_1490_, v_x_1491_, v_x_1492_);
    v_r_1494_ = leanh::lean_box((v_res_1493_) as usize);
    return v_r_1494_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq___redArg(
    mut v_inst_1495_: *mut leanh::LeanObject,
    mut v_x_1496_: *mut leanh::LeanObject,
    mut v_x_1497_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    v___x_1498_ = leanh::lean_apply_2(v_inst_1495_, v_x_1496_, v_x_1497_);
    v___x_1499_ = (leanh::lean_unbox(v___x_1498_) as u8);
    return v___x_1499_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq___redArg___boxed(
    mut v_inst_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
    mut v_x_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1503_: u8 = 0;
    let mut v_r_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l_Std_instDecidableEqRci_decEq___redArg(v_inst_1500_, v_x_1501_, v_x_1502_);
    v_r_1504_ = leanh::lean_box((v_res_1503_) as usize);
    return v_r_1504_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq(
    mut v_00_u03b1_1505_: *mut leanh::LeanObject,
    mut v_inst_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
    mut v_x_1508_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u8 = 0;
    v___x_1509_ = leanh::lean_apply_2(v_inst_1506_, v_x_1507_, v_x_1508_);
    v___x_1510_ = (leanh::lean_unbox(v___x_1509_) as u8);
    return v___x_1510_;
}
pub unsafe fn l_Std_instDecidableEqRci_decEq___boxed(
    mut v_00_u03b1_1511_: *mut leanh::LeanObject,
    mut v_inst_1512_: *mut leanh::LeanObject,
    mut v_x_1513_: *mut leanh::LeanObject,
    mut v_x_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1515_: u8 = 0;
    let mut v_r_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ =
        l_Std_instDecidableEqRci_decEq(v_00_u03b1_1511_, v_inst_1512_, v_x_1513_, v_x_1514_);
    v_r_1516_ = leanh::lean_box((v_res_1515_) as usize);
    return v_r_1516_;
}
pub unsafe fn l_Std_instDecidableEqRci___redArg(
    mut v_inst_1517_: *mut leanh::LeanObject,
    mut v_x_1518_: *mut leanh::LeanObject,
    mut v_x_1519_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    v___x_1520_ = leanh::lean_apply_2(v_inst_1517_, v_x_1518_, v_x_1519_);
    v___x_1521_ = (leanh::lean_unbox(v___x_1520_) as u8);
    return v___x_1521_;
}
pub unsafe fn l_Std_instDecidableEqRci___redArg___boxed(
    mut v_inst_1522_: *mut leanh::LeanObject,
    mut v_x_1523_: *mut leanh::LeanObject,
    mut v_x_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1525_: u8 = 0;
    let mut v_r_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Std_instDecidableEqRci___redArg(v_inst_1522_, v_x_1523_, v_x_1524_);
    v_r_1526_ = leanh::lean_box((v_res_1525_) as usize);
    return v_r_1526_;
}
pub unsafe fn l_Std_instDecidableEqRci(
    mut v_00_u03b1_1527_: *mut leanh::LeanObject,
    mut v_inst_1528_: *mut leanh::LeanObject,
    mut v_x_1529_: *mut leanh::LeanObject,
    mut v_x_1530_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    v___x_1531_ = leanh::lean_apply_2(v_inst_1528_, v_x_1529_, v_x_1530_);
    v___x_1532_ = (leanh::lean_unbox(v___x_1531_) as u8);
    return v___x_1532_;
}
pub unsafe fn l_Std_instDecidableEqRci___boxed(
    mut v_00_u03b1_1533_: *mut leanh::LeanObject,
    mut v_inst_1534_: *mut leanh::LeanObject,
    mut v_x_1535_: *mut leanh::LeanObject,
    mut v_x_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1537_: u8 = 0;
    let mut v_r_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_Std_instDecidableEqRci(v_00_u03b1_1533_, v_inst_1534_, v_x_1535_, v_x_1536_);
    v_r_1538_ = leanh::lean_box((v_res_1537_) as usize);
    return v_r_1538_;
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq___redArg(
    mut v_inst_1539_: *mut leanh::LeanObject,
    mut v_x_1540_: *mut leanh::LeanObject,
    mut v_x_1541_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: u8 = 0;
    v_lower_1542_ = leanh::lean_ctor_get(v_x_1540_, 0);
    leanh::lean_inc(v_lower_1542_);
    v_upper_1543_ = leanh::lean_ctor_get(v_x_1540_, 1);
    leanh::lean_inc(v_upper_1543_);
    leanh::lean_dec_ref(v_x_1540_);
    v_lower_1544_ = leanh::lean_ctor_get(v_x_1541_, 0);
    leanh::lean_inc(v_lower_1544_);
    v_upper_1545_ = leanh::lean_ctor_get(v_x_1541_, 1);
    leanh::lean_inc(v_upper_1545_);
    leanh::lean_dec_ref(v_x_1541_);
    leanh::lean_inc_ref(v_inst_1539_);
    v___x_1546_ = leanh::lean_apply_2(v_inst_1539_, v_lower_1542_, v_lower_1544_);
    v___x_1547_ = (leanh::lean_unbox(v___x_1546_) as u8);
    if v___x_1547_ == 0 {
        let mut v___x_1548_: u8 = 0;
        leanh::lean_dec(v_upper_1545_);
        leanh::lean_dec(v_upper_1543_);
        leanh::lean_dec_ref(v_inst_1539_);
        v___x_1548_ = (leanh::lean_unbox(v___x_1546_) as u8);
        return v___x_1548_;
    } else {
        let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1550_: u8 = 0;
        v___x_1549_ = leanh::lean_apply_2(v_inst_1539_, v_upper_1543_, v_upper_1545_);
        v___x_1550_ = (leanh::lean_unbox(v___x_1549_) as u8);
        return v___x_1550_;
    }
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq___redArg___boxed(
    mut v_inst_1551_: *mut leanh::LeanObject,
    mut v_x_1552_: *mut leanh::LeanObject,
    mut v_x_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: u8 = 0;
    let mut v_r_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1551_, v_x_1552_, v_x_1553_);
    v_r_1555_ = leanh::lean_box((v_res_1554_) as usize);
    return v_r_1555_;
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq(
    mut v_00_u03b1_1556_: *mut leanh::LeanObject,
    mut v_inst_1557_: *mut leanh::LeanObject,
    mut v_x_1558_: *mut leanh::LeanObject,
    mut v_x_1559_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1560_: u8 = 0;
    v___x_1560_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1557_, v_x_1558_, v_x_1559_);
    return v___x_1560_;
}
pub unsafe fn l_Std_instDecidableEqRoc_decEq___boxed(
    mut v_00_u03b1_1561_: *mut leanh::LeanObject,
    mut v_inst_1562_: *mut leanh::LeanObject,
    mut v_x_1563_: *mut leanh::LeanObject,
    mut v_x_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1565_: u8 = 0;
    let mut v_r_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1565_ =
        l_Std_instDecidableEqRoc_decEq(v_00_u03b1_1561_, v_inst_1562_, v_x_1563_, v_x_1564_);
    v_r_1566_ = leanh::lean_box((v_res_1565_) as usize);
    return v_r_1566_;
}
pub unsafe fn l_Std_instDecidableEqRoc___redArg(
    mut v_inst_1567_: *mut leanh::LeanObject,
    mut v_x_1568_: *mut leanh::LeanObject,
    mut v_x_1569_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1570_: u8 = 0;
    v___x_1570_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1567_, v_x_1568_, v_x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Std_instDecidableEqRoc___redArg___boxed(
    mut v_inst_1571_: *mut leanh::LeanObject,
    mut v_x_1572_: *mut leanh::LeanObject,
    mut v_x_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: u8 = 0;
    let mut v_r_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_instDecidableEqRoc___redArg(v_inst_1571_, v_x_1572_, v_x_1573_);
    v_r_1575_ = leanh::lean_box((v_res_1574_) as usize);
    return v_r_1575_;
}
pub unsafe fn l_Std_instDecidableEqRoc(
    mut v_00_u03b1_1576_: *mut leanh::LeanObject,
    mut v_inst_1577_: *mut leanh::LeanObject,
    mut v_x_1578_: *mut leanh::LeanObject,
    mut v_x_1579_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1580_: u8 = 0;
    v___x_1580_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_1577_, v_x_1578_, v_x_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Std_instDecidableEqRoc___boxed(
    mut v_00_u03b1_1581_: *mut leanh::LeanObject,
    mut v_inst_1582_: *mut leanh::LeanObject,
    mut v_x_1583_: *mut leanh::LeanObject,
    mut v_x_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1585_: u8 = 0;
    let mut v_r_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Std_instDecidableEqRoc(v_00_u03b1_1581_, v_inst_1582_, v_x_1583_, v_x_1584_);
    v_r_1586_ = leanh::lean_box((v_res_1585_) as usize);
    return v_r_1586_;
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq___redArg(
    mut v_inst_1587_: *mut leanh::LeanObject,
    mut v_x_1588_: *mut leanh::LeanObject,
    mut v_x_1589_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    v_lower_1590_ = leanh::lean_ctor_get(v_x_1588_, 0);
    leanh::lean_inc(v_lower_1590_);
    v_upper_1591_ = leanh::lean_ctor_get(v_x_1588_, 1);
    leanh::lean_inc(v_upper_1591_);
    leanh::lean_dec_ref(v_x_1588_);
    v_lower_1592_ = leanh::lean_ctor_get(v_x_1589_, 0);
    leanh::lean_inc(v_lower_1592_);
    v_upper_1593_ = leanh::lean_ctor_get(v_x_1589_, 1);
    leanh::lean_inc(v_upper_1593_);
    leanh::lean_dec_ref(v_x_1589_);
    leanh::lean_inc_ref(v_inst_1587_);
    v___x_1594_ = leanh::lean_apply_2(v_inst_1587_, v_lower_1590_, v_lower_1592_);
    v___x_1595_ = (leanh::lean_unbox(v___x_1594_) as u8);
    if v___x_1595_ == 0 {
        let mut v___x_1596_: u8 = 0;
        leanh::lean_dec(v_upper_1593_);
        leanh::lean_dec(v_upper_1591_);
        leanh::lean_dec_ref(v_inst_1587_);
        v___x_1596_ = (leanh::lean_unbox(v___x_1594_) as u8);
        return v___x_1596_;
    } else {
        let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1598_: u8 = 0;
        v___x_1597_ = leanh::lean_apply_2(v_inst_1587_, v_upper_1591_, v_upper_1593_);
        v___x_1598_ = (leanh::lean_unbox(v___x_1597_) as u8);
        return v___x_1598_;
    }
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq___redArg___boxed(
    mut v_inst_1599_: *mut leanh::LeanObject,
    mut v_x_1600_: *mut leanh::LeanObject,
    mut v_x_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1602_: u8 = 0;
    let mut v_r_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1599_, v_x_1600_, v_x_1601_);
    v_r_1603_ = leanh::lean_box((v_res_1602_) as usize);
    return v_r_1603_;
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq(
    mut v_00_u03b1_1604_: *mut leanh::LeanObject,
    mut v_inst_1605_: *mut leanh::LeanObject,
    mut v_x_1606_: *mut leanh::LeanObject,
    mut v_x_1607_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1608_: u8 = 0;
    v___x_1608_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1605_, v_x_1606_, v_x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Std_instDecidableEqRoo_decEq___boxed(
    mut v_00_u03b1_1609_: *mut leanh::LeanObject,
    mut v_inst_1610_: *mut leanh::LeanObject,
    mut v_x_1611_: *mut leanh::LeanObject,
    mut v_x_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: u8 = 0;
    let mut v_r_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ =
        l_Std_instDecidableEqRoo_decEq(v_00_u03b1_1609_, v_inst_1610_, v_x_1611_, v_x_1612_);
    v_r_1614_ = leanh::lean_box((v_res_1613_) as usize);
    return v_r_1614_;
}
pub unsafe fn l_Std_instDecidableEqRoo___redArg(
    mut v_inst_1615_: *mut leanh::LeanObject,
    mut v_x_1616_: *mut leanh::LeanObject,
    mut v_x_1617_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1618_: u8 = 0;
    v___x_1618_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1615_, v_x_1616_, v_x_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Std_instDecidableEqRoo___redArg___boxed(
    mut v_inst_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: *mut leanh::LeanObject,
    mut v_x_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1622_: u8 = 0;
    let mut v_r_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Std_instDecidableEqRoo___redArg(v_inst_1619_, v_x_1620_, v_x_1621_);
    v_r_1623_ = leanh::lean_box((v_res_1622_) as usize);
    return v_r_1623_;
}
pub unsafe fn l_Std_instDecidableEqRoo(
    mut v_00_u03b1_1624_: *mut leanh::LeanObject,
    mut v_inst_1625_: *mut leanh::LeanObject,
    mut v_x_1626_: *mut leanh::LeanObject,
    mut v_x_1627_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1628_: u8 = 0;
    v___x_1628_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_1625_, v_x_1626_, v_x_1627_);
    return v___x_1628_;
}
pub unsafe fn l_Std_instDecidableEqRoo___boxed(
    mut v_00_u03b1_1629_: *mut leanh::LeanObject,
    mut v_inst_1630_: *mut leanh::LeanObject,
    mut v_x_1631_: *mut leanh::LeanObject,
    mut v_x_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1633_: u8 = 0;
    let mut v_r_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Std_instDecidableEqRoo(v_00_u03b1_1629_, v_inst_1630_, v_x_1631_, v_x_1632_);
    v_r_1634_ = leanh::lean_box((v_res_1633_) as usize);
    return v_r_1634_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq___redArg(
    mut v_inst_1635_: *mut leanh::LeanObject,
    mut v_x_1636_: *mut leanh::LeanObject,
    mut v_x_1637_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    v___x_1638_ = leanh::lean_apply_2(v_inst_1635_, v_x_1636_, v_x_1637_);
    v___x_1639_ = (leanh::lean_unbox(v___x_1638_) as u8);
    return v___x_1639_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq___redArg___boxed(
    mut v_inst_1640_: *mut leanh::LeanObject,
    mut v_x_1641_: *mut leanh::LeanObject,
    mut v_x_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1643_: u8 = 0;
    let mut v_r_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Std_instDecidableEqRoi_decEq___redArg(v_inst_1640_, v_x_1641_, v_x_1642_);
    v_r_1644_ = leanh::lean_box((v_res_1643_) as usize);
    return v_r_1644_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq(
    mut v_00_u03b1_1645_: *mut leanh::LeanObject,
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_x_1647_: *mut leanh::LeanObject,
    mut v_x_1648_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    v___x_1649_ = leanh::lean_apply_2(v_inst_1646_, v_x_1647_, v_x_1648_);
    v___x_1650_ = (leanh::lean_unbox(v___x_1649_) as u8);
    return v___x_1650_;
}
pub unsafe fn l_Std_instDecidableEqRoi_decEq___boxed(
    mut v_00_u03b1_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_x_1653_: *mut leanh::LeanObject,
    mut v_x_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: u8 = 0;
    let mut v_r_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ =
        l_Std_instDecidableEqRoi_decEq(v_00_u03b1_1651_, v_inst_1652_, v_x_1653_, v_x_1654_);
    v_r_1656_ = leanh::lean_box((v_res_1655_) as usize);
    return v_r_1656_;
}
pub unsafe fn l_Std_instDecidableEqRoi___redArg(
    mut v_inst_1657_: *mut leanh::LeanObject,
    mut v_x_1658_: *mut leanh::LeanObject,
    mut v_x_1659_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    v___x_1660_ = leanh::lean_apply_2(v_inst_1657_, v_x_1658_, v_x_1659_);
    v___x_1661_ = (leanh::lean_unbox(v___x_1660_) as u8);
    return v___x_1661_;
}
pub unsafe fn l_Std_instDecidableEqRoi___redArg___boxed(
    mut v_inst_1662_: *mut leanh::LeanObject,
    mut v_x_1663_: *mut leanh::LeanObject,
    mut v_x_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1665_: u8 = 0;
    let mut v_r_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1665_ = l_Std_instDecidableEqRoi___redArg(v_inst_1662_, v_x_1663_, v_x_1664_);
    v_r_1666_ = leanh::lean_box((v_res_1665_) as usize);
    return v_r_1666_;
}
pub unsafe fn l_Std_instDecidableEqRoi(
    mut v_00_u03b1_1667_: *mut leanh::LeanObject,
    mut v_inst_1668_: *mut leanh::LeanObject,
    mut v_x_1669_: *mut leanh::LeanObject,
    mut v_x_1670_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    v___x_1671_ = leanh::lean_apply_2(v_inst_1668_, v_x_1669_, v_x_1670_);
    v___x_1672_ = (leanh::lean_unbox(v___x_1671_) as u8);
    return v___x_1672_;
}
pub unsafe fn l_Std_instDecidableEqRoi___boxed(
    mut v_00_u03b1_1673_: *mut leanh::LeanObject,
    mut v_inst_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1677_: u8 = 0;
    let mut v_r_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Std_instDecidableEqRoi(v_00_u03b1_1673_, v_inst_1674_, v_x_1675_, v_x_1676_);
    v_r_1678_ = leanh::lean_box((v_res_1677_) as usize);
    return v_r_1678_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq___redArg(
    mut v_inst_1679_: *mut leanh::LeanObject,
    mut v_x_1680_: *mut leanh::LeanObject,
    mut v_x_1681_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: u8 = 0;
    v___x_1682_ = leanh::lean_apply_2(v_inst_1679_, v_x_1680_, v_x_1681_);
    v___x_1683_ = (leanh::lean_unbox(v___x_1682_) as u8);
    return v___x_1683_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq___redArg___boxed(
    mut v_inst_1684_: *mut leanh::LeanObject,
    mut v_x_1685_: *mut leanh::LeanObject,
    mut v_x_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1687_: u8 = 0;
    let mut v_r_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Std_instDecidableEqRic_decEq___redArg(v_inst_1684_, v_x_1685_, v_x_1686_);
    v_r_1688_ = leanh::lean_box((v_res_1687_) as usize);
    return v_r_1688_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq(
    mut v_00_u03b1_1689_: *mut leanh::LeanObject,
    mut v_inst_1690_: *mut leanh::LeanObject,
    mut v_x_1691_: *mut leanh::LeanObject,
    mut v_x_1692_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    v___x_1693_ = leanh::lean_apply_2(v_inst_1690_, v_x_1691_, v_x_1692_);
    v___x_1694_ = (leanh::lean_unbox(v___x_1693_) as u8);
    return v___x_1694_;
}
pub unsafe fn l_Std_instDecidableEqRic_decEq___boxed(
    mut v_00_u03b1_1695_: *mut leanh::LeanObject,
    mut v_inst_1696_: *mut leanh::LeanObject,
    mut v_x_1697_: *mut leanh::LeanObject,
    mut v_x_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1699_: u8 = 0;
    let mut v_r_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ =
        l_Std_instDecidableEqRic_decEq(v_00_u03b1_1695_, v_inst_1696_, v_x_1697_, v_x_1698_);
    v_r_1700_ = leanh::lean_box((v_res_1699_) as usize);
    return v_r_1700_;
}
pub unsafe fn l_Std_instDecidableEqRic___redArg(
    mut v_inst_1701_: *mut leanh::LeanObject,
    mut v_x_1702_: *mut leanh::LeanObject,
    mut v_x_1703_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    v___x_1704_ = leanh::lean_apply_2(v_inst_1701_, v_x_1702_, v_x_1703_);
    v___x_1705_ = (leanh::lean_unbox(v___x_1704_) as u8);
    return v___x_1705_;
}
pub unsafe fn l_Std_instDecidableEqRic___redArg___boxed(
    mut v_inst_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_x_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1709_: u8 = 0;
    let mut v_r_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Std_instDecidableEqRic___redArg(v_inst_1706_, v_x_1707_, v_x_1708_);
    v_r_1710_ = leanh::lean_box((v_res_1709_) as usize);
    return v_r_1710_;
}
pub unsafe fn l_Std_instDecidableEqRic(
    mut v_00_u03b1_1711_: *mut leanh::LeanObject,
    mut v_inst_1712_: *mut leanh::LeanObject,
    mut v_x_1713_: *mut leanh::LeanObject,
    mut v_x_1714_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    v___x_1715_ = leanh::lean_apply_2(v_inst_1712_, v_x_1713_, v_x_1714_);
    v___x_1716_ = (leanh::lean_unbox(v___x_1715_) as u8);
    return v___x_1716_;
}
pub unsafe fn l_Std_instDecidableEqRic___boxed(
    mut v_00_u03b1_1717_: *mut leanh::LeanObject,
    mut v_inst_1718_: *mut leanh::LeanObject,
    mut v_x_1719_: *mut leanh::LeanObject,
    mut v_x_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1721_: u8 = 0;
    let mut v_r_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Std_instDecidableEqRic(v_00_u03b1_1717_, v_inst_1718_, v_x_1719_, v_x_1720_);
    v_r_1722_ = leanh::lean_box((v_res_1721_) as usize);
    return v_r_1722_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq___redArg(
    mut v_inst_1723_: *mut leanh::LeanObject,
    mut v_x_1724_: *mut leanh::LeanObject,
    mut v_x_1725_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    v___x_1726_ = leanh::lean_apply_2(v_inst_1723_, v_x_1724_, v_x_1725_);
    v___x_1727_ = (leanh::lean_unbox(v___x_1726_) as u8);
    return v___x_1727_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq___redArg___boxed(
    mut v_inst_1728_: *mut leanh::LeanObject,
    mut v_x_1729_: *mut leanh::LeanObject,
    mut v_x_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1731_: u8 = 0;
    let mut v_r_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Std_instDecidableEqRio_decEq___redArg(v_inst_1728_, v_x_1729_, v_x_1730_);
    v_r_1732_ = leanh::lean_box((v_res_1731_) as usize);
    return v_r_1732_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq(
    mut v_00_u03b1_1733_: *mut leanh::LeanObject,
    mut v_inst_1734_: *mut leanh::LeanObject,
    mut v_x_1735_: *mut leanh::LeanObject,
    mut v_x_1736_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    v___x_1737_ = leanh::lean_apply_2(v_inst_1734_, v_x_1735_, v_x_1736_);
    v___x_1738_ = (leanh::lean_unbox(v___x_1737_) as u8);
    return v___x_1738_;
}
pub unsafe fn l_Std_instDecidableEqRio_decEq___boxed(
    mut v_00_u03b1_1739_: *mut leanh::LeanObject,
    mut v_inst_1740_: *mut leanh::LeanObject,
    mut v_x_1741_: *mut leanh::LeanObject,
    mut v_x_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1743_: u8 = 0;
    let mut v_r_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1743_ =
        l_Std_instDecidableEqRio_decEq(v_00_u03b1_1739_, v_inst_1740_, v_x_1741_, v_x_1742_);
    v_r_1744_ = leanh::lean_box((v_res_1743_) as usize);
    return v_r_1744_;
}
pub unsafe fn l_Std_instDecidableEqRio___redArg(
    mut v_inst_1745_: *mut leanh::LeanObject,
    mut v_x_1746_: *mut leanh::LeanObject,
    mut v_x_1747_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    v___x_1748_ = leanh::lean_apply_2(v_inst_1745_, v_x_1746_, v_x_1747_);
    v___x_1749_ = (leanh::lean_unbox(v___x_1748_) as u8);
    return v___x_1749_;
}
pub unsafe fn l_Std_instDecidableEqRio___redArg___boxed(
    mut v_inst_1750_: *mut leanh::LeanObject,
    mut v_x_1751_: *mut leanh::LeanObject,
    mut v_x_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1753_: u8 = 0;
    let mut v_r_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Std_instDecidableEqRio___redArg(v_inst_1750_, v_x_1751_, v_x_1752_);
    v_r_1754_ = leanh::lean_box((v_res_1753_) as usize);
    return v_r_1754_;
}
pub unsafe fn l_Std_instDecidableEqRio(
    mut v_00_u03b1_1755_: *mut leanh::LeanObject,
    mut v_inst_1756_: *mut leanh::LeanObject,
    mut v_x_1757_: *mut leanh::LeanObject,
    mut v_x_1758_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    v___x_1759_ = leanh::lean_apply_2(v_inst_1756_, v_x_1757_, v_x_1758_);
    v___x_1760_ = (leanh::lean_unbox(v___x_1759_) as u8);
    return v___x_1760_;
}
pub unsafe fn l_Std_instDecidableEqRio___boxed(
    mut v_00_u03b1_1761_: *mut leanh::LeanObject,
    mut v_inst_1762_: *mut leanh::LeanObject,
    mut v_x_1763_: *mut leanh::LeanObject,
    mut v_x_1764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1765_: u8 = 0;
    let mut v_r_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1765_ = l_Std_instDecidableEqRio(v_00_u03b1_1761_, v_inst_1762_, v_x_1763_, v_x_1764_);
    v_r_1766_ = leanh::lean_box((v_res_1765_) as usize);
    return v_r_1766_;
}
pub unsafe fn l_Std_instDecidableEqRii_decEq(
    mut v_00_u03b1_1767_: *mut leanh::LeanObject,
    mut v_inst_1768_: *mut leanh::LeanObject,
    mut v_x_1769_: *mut leanh::LeanObject,
    mut v_x_1770_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1771_: u8 = 0;
    v___x_1771_ = 1;
    return v___x_1771_;
}
pub unsafe fn l_Std_instDecidableEqRii_decEq___boxed(
    mut v_00_u03b1_1772_: *mut leanh::LeanObject,
    mut v_inst_1773_: *mut leanh::LeanObject,
    mut v_x_1774_: *mut leanh::LeanObject,
    mut v_x_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1776_: u8 = 0;
    let mut v_r_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ =
        l_Std_instDecidableEqRii_decEq(v_00_u03b1_1772_, v_inst_1773_, v_x_1774_, v_x_1775_);
    leanh::lean_dec_ref(v_inst_1773_);
    v_r_1777_ = leanh::lean_box((v_res_1776_) as usize);
    return v_r_1777_;
}
pub unsafe fn l_Std_instDecidableEqRii(
    mut v_00_u03b1_1778_: *mut leanh::LeanObject,
    mut v_inst_1779_: *mut leanh::LeanObject,
    mut v_x_1780_: *mut leanh::LeanObject,
    mut v_x_1781_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1782_: u8 = 0;
    v___x_1782_ = 1;
    return v___x_1782_;
}
pub unsafe fn l_Std_instDecidableEqRii___boxed(
    mut v_00_u03b1_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_x_1785_: *mut leanh::LeanObject,
    mut v_x_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1787_: u8 = 0;
    let mut v_r_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1787_ = l_Std_instDecidableEqRii(v_00_u03b1_1783_, v_inst_1784_, v_x_1785_, v_x_1786_);
    leanh::lean_dec_ref(v_inst_1784_);
    v_r_1788_ = leanh::lean_box((v_res_1787_) as usize);
    return v_r_1788_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5;
    v___x_1998_ = l_String_toRawSubstring_x27(v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(
    mut v_x_2022_: *mut leanh::LeanObject,
    mut v_a_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    v___x_2025_ = l_Std_term___x2e_x2e_x2e_x3d___00__closed__1;
    leanh::lean_inc(v_x_2022_);
    v___x_2026_ = l_Lean_Syntax_isOfKind(v_x_2022_, v___x_2025_);
    if v___x_2026_ == 0 {
        let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2022_);
        v___x_2027_ = leanh::lean_box(1);
        v___x_2028_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2028_, 0, v___x_2027_);
        leanh::lean_ctor_set(v___x_2028_, 1, v_a_2024_);
        return v___x_2028_;
    } else {
        let mut v_quotContext_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: u8 = 0;
        let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2029_ = leanh::lean_ctor_get(v_a_2023_, 1);
        v_currMacroScope_2030_ = leanh::lean_ctor_get(v_a_2023_, 2);
        v_ref_2031_ = leanh::lean_ctor_get(v_a_2023_, 5);
        v___x_2032_ = leanh::lean_unsigned_to_nat(0);
        v___x_2033_ = l_Lean_Syntax_getArg(v_x_2022_, v___x_2032_);
        v___x_2034_ = leanh::lean_unsigned_to_nat(2);
        v___x_2035_ = l_Lean_Syntax_getArg(v_x_2022_, v___x_2034_);
        leanh::lean_dec(v_x_2022_);
        v___x_2036_ = 0;
        v___x_2037_ = l_Lean_SourceInfo_fromRef(v_ref_2031_, v___x_2036_);
        v___x_2038_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6);
        v___x_2040_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9;
        leanh::lean_inc(v_currMacroScope_2030_);
        leanh::lean_inc(v_quotContext_2029_);
        v___x_2041_ =
            l_Lean_addMacroScope(v_quotContext_2029_, v___x_2040_, v_currMacroScope_2030_);
        v___x_2042_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14;
        leanh::lean_inc_n(v___x_2037_, 2);
        v___x_2043_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2043_, 0, v___x_2037_);
        leanh::lean_ctor_set(v___x_2043_, 1, v___x_2039_);
        leanh::lean_ctor_set(v___x_2043_, 2, v___x_2041_);
        leanh::lean_ctor_set(v___x_2043_, 3, v___x_2042_);
        v___x_2044_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2045_ = l_Lean_Syntax_node2(v___x_2037_, v___x_2044_, v___x_2033_, v___x_2035_);
        v___x_2046_ = l_Lean_Syntax_node2(v___x_2037_, v___x_2038_, v___x_2043_, v___x_2045_);
        v___x_2047_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
        leanh::lean_ctor_set(v___x_2047_, 1, v_a_2024_);
        return v___x_2047_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___boxed(
    mut v_x_2048_: *mut leanh::LeanObject,
    mut v_a_2049_: *mut leanh::LeanObject,
    mut v_a_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(v_x_2048_, v_a_2049_, v_a_2050_);
    leanh::lean_dec_ref(v_a_2049_);
    return v_res_2051_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0;
    v___x_2054_ = l_String_toRawSubstring_x27(v___x_2053_);
    return v___x_2054_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(
    mut v_x_2074_: *mut leanh::LeanObject,
    mut v_a_2075_: *mut leanh::LeanObject,
    mut v_a_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    v___x_2077_ = l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1;
    leanh::lean_inc(v_x_2074_);
    v___x_2078_ = l_Lean_Syntax_isOfKind(v_x_2074_, v___x_2077_);
    if v___x_2078_ == 0 {
        let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2074_);
        v___x_2079_ = leanh::lean_box(1);
        v___x_2080_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2080_, 0, v___x_2079_);
        leanh::lean_ctor_set(v___x_2080_, 1, v_a_2076_);
        return v___x_2080_;
    } else {
        let mut v_quotContext_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: u8 = 0;
        let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2081_ = leanh::lean_ctor_get(v_a_2075_, 1);
        v_currMacroScope_2082_ = leanh::lean_ctor_get(v_a_2075_, 2);
        v_ref_2083_ = leanh::lean_ctor_get(v_a_2075_, 5);
        v___x_2084_ = leanh::lean_unsigned_to_nat(1);
        v___x_2085_ = l_Lean_Syntax_getArg(v_x_2074_, v___x_2084_);
        leanh::lean_dec(v_x_2074_);
        v___x_2086_ = 0;
        v___x_2087_ = l_Lean_SourceInfo_fromRef(v_ref_2083_, v___x_2086_);
        v___x_2088_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2089_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1);
        v___x_2090_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2082_);
        leanh::lean_inc(v_quotContext_2081_);
        v___x_2091_ =
            l_Lean_addMacroScope(v_quotContext_2081_, v___x_2090_, v_currMacroScope_2082_);
        v___x_2092_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8;
        leanh::lean_inc_n(v___x_2087_, 2);
        v___x_2093_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2093_, 0, v___x_2087_);
        leanh::lean_ctor_set(v___x_2093_, 1, v___x_2089_);
        leanh::lean_ctor_set(v___x_2093_, 2, v___x_2091_);
        leanh::lean_ctor_set(v___x_2093_, 3, v___x_2092_);
        v___x_2094_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2095_ = l_Lean_Syntax_node1(v___x_2087_, v___x_2094_, v___x_2085_);
        v___x_2096_ = l_Lean_Syntax_node2(v___x_2087_, v___x_2088_, v___x_2093_, v___x_2095_);
        v___x_2097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2097_, 0, v___x_2096_);
        leanh::lean_ctor_set(v___x_2097_, 1, v_a_2076_);
        return v___x_2097_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___boxed(
    mut v_x_2098_: *mut leanh::LeanObject,
    mut v_a_2099_: *mut leanh::LeanObject,
    mut v_a_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(v_x_2098_, v_a_2099_, v_a_2100_);
    leanh::lean_dec_ref(v_a_2099_);
    return v_res_2101_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2103_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0;
    v___x_2104_ = l_String_toRawSubstring_x27(v___x_2103_);
    return v___x_2104_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(
    mut v_x_2124_: *mut leanh::LeanObject,
    mut v_a_2125_: *mut leanh::LeanObject,
    mut v_a_2126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    v___x_2127_ = l_Std_term___x2e_x2e_x2e_x2a___closed__2;
    leanh::lean_inc(v_x_2124_);
    v___x_2128_ = l_Lean_Syntax_isOfKind(v_x_2124_, v___x_2127_);
    if v___x_2128_ == 0 {
        let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2124_);
        v___x_2129_ = leanh::lean_box(1);
        v___x_2130_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2130_, 0, v___x_2129_);
        leanh::lean_ctor_set(v___x_2130_, 1, v_a_2126_);
        return v___x_2130_;
    } else {
        let mut v_quotContext_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: u8 = 0;
        let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2131_ = leanh::lean_ctor_get(v_a_2125_, 1);
        v_currMacroScope_2132_ = leanh::lean_ctor_get(v_a_2125_, 2);
        v_ref_2133_ = leanh::lean_ctor_get(v_a_2125_, 5);
        v___x_2134_ = leanh::lean_unsigned_to_nat(0);
        v___x_2135_ = l_Lean_Syntax_getArg(v_x_2124_, v___x_2134_);
        leanh::lean_dec(v_x_2124_);
        v___x_2136_ = 0;
        v___x_2137_ = l_Lean_SourceInfo_fromRef(v_ref_2133_, v___x_2136_);
        v___x_2138_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2139_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1);
        v___x_2140_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3;
        leanh::lean_inc(v_currMacroScope_2132_);
        leanh::lean_inc(v_quotContext_2131_);
        v___x_2141_ =
            l_Lean_addMacroScope(v_quotContext_2131_, v___x_2140_, v_currMacroScope_2132_);
        v___x_2142_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8;
        leanh::lean_inc_n(v___x_2137_, 2);
        v___x_2143_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2143_, 0, v___x_2137_);
        leanh::lean_ctor_set(v___x_2143_, 1, v___x_2139_);
        leanh::lean_ctor_set(v___x_2143_, 2, v___x_2141_);
        leanh::lean_ctor_set(v___x_2143_, 3, v___x_2142_);
        v___x_2144_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2145_ = l_Lean_Syntax_node1(v___x_2137_, v___x_2144_, v___x_2135_);
        v___x_2146_ = l_Lean_Syntax_node2(v___x_2137_, v___x_2138_, v___x_2143_, v___x_2145_);
        v___x_2147_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
        leanh::lean_ctor_set(v___x_2147_, 1, v_a_2126_);
        return v___x_2147_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___boxed(
    mut v_x_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(v_x_2148_, v_a_2149_, v_a_2150_);
    leanh::lean_dec_ref(v_a_2149_);
    return v_res_2151_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0;
    v___x_2154_ = l_String_toRawSubstring_x27(v___x_2153_);
    return v___x_2154_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(
    mut v_x_2174_: *mut leanh::LeanObject,
    mut v_a_2175_: *mut leanh::LeanObject,
    mut v_a_2176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    v___x_2177_ = l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1;
    v___x_2178_ = l_Lean_Syntax_isOfKind(v_x_2174_, v___x_2177_);
    if v___x_2178_ == 0 {
        let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2179_ = leanh::lean_box(1);
        v___x_2180_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2180_, 0, v___x_2179_);
        leanh::lean_ctor_set(v___x_2180_, 1, v_a_2176_);
        return v___x_2180_;
    } else {
        let mut v_quotContext_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2184_: u8 = 0;
        let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2181_ = leanh::lean_ctor_get(v_a_2175_, 1);
        v_currMacroScope_2182_ = leanh::lean_ctor_get(v_a_2175_, 2);
        v_ref_2183_ = leanh::lean_ctor_get(v_a_2175_, 5);
        v___x_2184_ = 0;
        v___x_2185_ = l_Lean_SourceInfo_fromRef(v_ref_2183_, v___x_2184_);
        v___x_2186_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1);
        v___x_2187_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3;
        leanh::lean_inc(v_currMacroScope_2182_);
        leanh::lean_inc(v_quotContext_2181_);
        v___x_2188_ =
            l_Lean_addMacroScope(v_quotContext_2181_, v___x_2187_, v_currMacroScope_2182_);
        v___x_2189_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8;
        v___x_2190_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2190_, 0, v___x_2185_);
        leanh::lean_ctor_set(v___x_2190_, 1, v___x_2186_);
        leanh::lean_ctor_set(v___x_2190_, 2, v___x_2188_);
        leanh::lean_ctor_set(v___x_2190_, 3, v___x_2189_);
        v___x_2191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2191_, 0, v___x_2190_);
        leanh::lean_ctor_set(v___x_2191_, 1, v_a_2176_);
        return v___x_2191_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___boxed(
    mut v_x_2192_: *mut leanh::LeanObject,
    mut v_a_2193_: *mut leanh::LeanObject,
    mut v_a_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(v_x_2192_, v_a_2193_, v_a_2194_);
    leanh::lean_dec_ref(v_a_2193_);
    return v_res_2195_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0;
    v___x_2198_ = l_String_toRawSubstring_x27(v___x_2197_);
    return v___x_2198_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(
    mut v_x_2218_: *mut leanh::LeanObject,
    mut v_a_2219_: *mut leanh::LeanObject,
    mut v_a_2220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    v___x_2221_ = l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1;
    leanh::lean_inc(v_x_2218_);
    v___x_2222_ = l_Lean_Syntax_isOfKind(v_x_2218_, v___x_2221_);
    if v___x_2222_ == 0 {
        let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2218_);
        v___x_2223_ = leanh::lean_box(1);
        v___x_2224_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
        leanh::lean_ctor_set(v___x_2224_, 1, v_a_2220_);
        return v___x_2224_;
    } else {
        let mut v_quotContext_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2232_: u8 = 0;
        let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2225_ = leanh::lean_ctor_get(v_a_2219_, 1);
        v_currMacroScope_2226_ = leanh::lean_ctor_get(v_a_2219_, 2);
        v_ref_2227_ = leanh::lean_ctor_get(v_a_2219_, 5);
        v___x_2228_ = leanh::lean_unsigned_to_nat(0);
        v___x_2229_ = l_Lean_Syntax_getArg(v_x_2218_, v___x_2228_);
        v___x_2230_ = leanh::lean_unsigned_to_nat(2);
        v___x_2231_ = l_Lean_Syntax_getArg(v_x_2218_, v___x_2230_);
        leanh::lean_dec(v_x_2218_);
        v___x_2232_ = 0;
        v___x_2233_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2232_);
        v___x_2234_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2235_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1);
        v___x_2236_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2226_);
        leanh::lean_inc(v_quotContext_2225_);
        v___x_2237_ =
            l_Lean_addMacroScope(v_quotContext_2225_, v___x_2236_, v_currMacroScope_2226_);
        v___x_2238_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8;
        leanh::lean_inc_n(v___x_2233_, 2);
        v___x_2239_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2239_, 0, v___x_2233_);
        leanh::lean_ctor_set(v___x_2239_, 1, v___x_2235_);
        leanh::lean_ctor_set(v___x_2239_, 2, v___x_2237_);
        leanh::lean_ctor_set(v___x_2239_, 3, v___x_2238_);
        v___x_2240_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2241_ = l_Lean_Syntax_node2(v___x_2233_, v___x_2240_, v___x_2229_, v___x_2231_);
        v___x_2242_ = l_Lean_Syntax_node2(v___x_2233_, v___x_2234_, v___x_2239_, v___x_2241_);
        v___x_2243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2243_, 0, v___x_2242_);
        leanh::lean_ctor_set(v___x_2243_, 1, v_a_2220_);
        return v___x_2243_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___boxed(
    mut v_x_2244_: *mut leanh::LeanObject,
    mut v_a_2245_: *mut leanh::LeanObject,
    mut v_a_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(v_x_2244_, v_a_2245_, v_a_2246_);
    leanh::lean_dec_ref(v_a_2245_);
    return v_res_2247_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0;
    v___x_2250_ = l_String_toRawSubstring_x27(v___x_2249_);
    return v___x_2250_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(
    mut v_x_2270_: *mut leanh::LeanObject,
    mut v_a_2271_: *mut leanh::LeanObject,
    mut v_a_2272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    v___x_2273_ = l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1;
    leanh::lean_inc(v_x_2270_);
    v___x_2274_ = l_Lean_Syntax_isOfKind(v_x_2270_, v___x_2273_);
    if v___x_2274_ == 0 {
        let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2270_);
        v___x_2275_ = leanh::lean_box(1);
        v___x_2276_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
        leanh::lean_ctor_set(v___x_2276_, 1, v_a_2272_);
        return v___x_2276_;
    } else {
        let mut v_quotContext_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2282_: u8 = 0;
        let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2277_ = leanh::lean_ctor_get(v_a_2271_, 1);
        v_currMacroScope_2278_ = leanh::lean_ctor_get(v_a_2271_, 2);
        v_ref_2279_ = leanh::lean_ctor_get(v_a_2271_, 5);
        v___x_2280_ = leanh::lean_unsigned_to_nat(0);
        v___x_2281_ = l_Lean_Syntax_getArg(v_x_2270_, v___x_2280_);
        leanh::lean_dec(v_x_2270_);
        v___x_2282_ = 0;
        v___x_2283_ = l_Lean_SourceInfo_fromRef(v_ref_2279_, v___x_2282_);
        v___x_2284_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1);
        v___x_2286_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3;
        leanh::lean_inc(v_currMacroScope_2278_);
        leanh::lean_inc(v_quotContext_2277_);
        v___x_2287_ =
            l_Lean_addMacroScope(v_quotContext_2277_, v___x_2286_, v_currMacroScope_2278_);
        v___x_2288_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8;
        leanh::lean_inc_n(v___x_2283_, 2);
        v___x_2289_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2289_, 0, v___x_2283_);
        leanh::lean_ctor_set(v___x_2289_, 1, v___x_2285_);
        leanh::lean_ctor_set(v___x_2289_, 2, v___x_2287_);
        leanh::lean_ctor_set(v___x_2289_, 3, v___x_2288_);
        v___x_2290_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2291_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2290_, v___x_2281_);
        v___x_2292_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2284_, v___x_2289_, v___x_2291_);
        v___x_2293_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
        leanh::lean_ctor_set(v___x_2293_, 1, v_a_2272_);
        return v___x_2293_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___boxed(
    mut v_x_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2297_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(v_x_2294_, v_a_2295_, v_a_2296_);
    leanh::lean_dec_ref(v_a_2295_);
    return v_res_2297_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0;
    v___x_2300_ = l_String_toRawSubstring_x27(v___x_2299_);
    return v___x_2300_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(
    mut v_x_2320_: *mut leanh::LeanObject,
    mut v_a_2321_: *mut leanh::LeanObject,
    mut v_a_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    v___x_2323_ = l_Std_term___x2e_x2e_x2e_x3c___00__closed__1;
    leanh::lean_inc(v_x_2320_);
    v___x_2324_ = l_Lean_Syntax_isOfKind(v_x_2320_, v___x_2323_);
    if v___x_2324_ == 0 {
        let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2320_);
        v___x_2325_ = leanh::lean_box(1);
        v___x_2326_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2326_, 0, v___x_2325_);
        leanh::lean_ctor_set(v___x_2326_, 1, v_a_2322_);
        return v___x_2326_;
    } else {
        let mut v_quotContext_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2334_: u8 = 0;
        let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2327_ = leanh::lean_ctor_get(v_a_2321_, 1);
        v_currMacroScope_2328_ = leanh::lean_ctor_get(v_a_2321_, 2);
        v_ref_2329_ = leanh::lean_ctor_get(v_a_2321_, 5);
        v___x_2330_ = leanh::lean_unsigned_to_nat(0);
        v___x_2331_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2330_);
        v___x_2332_ = leanh::lean_unsigned_to_nat(2);
        v___x_2333_ = l_Lean_Syntax_getArg(v_x_2320_, v___x_2332_);
        leanh::lean_dec(v_x_2320_);
        v___x_2334_ = 0;
        v___x_2335_ = l_Lean_SourceInfo_fromRef(v_ref_2329_, v___x_2334_);
        v___x_2336_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2337_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2338_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2328_);
        leanh::lean_inc(v_quotContext_2327_);
        v___x_2339_ =
            l_Lean_addMacroScope(v_quotContext_2327_, v___x_2338_, v_currMacroScope_2328_);
        v___x_2340_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8;
        leanh::lean_inc_n(v___x_2335_, 2);
        v___x_2341_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2341_, 0, v___x_2335_);
        leanh::lean_ctor_set(v___x_2341_, 1, v___x_2337_);
        leanh::lean_ctor_set(v___x_2341_, 2, v___x_2339_);
        leanh::lean_ctor_set(v___x_2341_, 3, v___x_2340_);
        v___x_2342_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2343_ = l_Lean_Syntax_node2(v___x_2335_, v___x_2342_, v___x_2331_, v___x_2333_);
        v___x_2344_ = l_Lean_Syntax_node2(v___x_2335_, v___x_2336_, v___x_2341_, v___x_2343_);
        v___x_2345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2345_, 0, v___x_2344_);
        leanh::lean_ctor_set(v___x_2345_, 1, v_a_2322_);
        return v___x_2345_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___boxed(
    mut v_x_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
    mut v_a_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(v_x_2346_, v_a_2347_, v_a_2348_);
    leanh::lean_dec_ref(v_a_2347_);
    return v_res_2349_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(
    mut v_x_2350_: *mut leanh::LeanObject,
    mut v_a_2351_: *mut leanh::LeanObject,
    mut v_a_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: u8 = 0;
    v___x_2353_ = l_Std_term___x2e_x2e_x2e___00__closed__1;
    leanh::lean_inc(v_x_2350_);
    v___x_2354_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2353_);
    if v___x_2354_ == 0 {
        let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2350_);
        v___x_2355_ = leanh::lean_box(1);
        v___x_2356_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2356_, 0, v___x_2355_);
        leanh::lean_ctor_set(v___x_2356_, 1, v_a_2352_);
        return v___x_2356_;
    } else {
        let mut v_quotContext_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2364_: u8 = 0;
        let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2357_ = leanh::lean_ctor_get(v_a_2351_, 1);
        v_currMacroScope_2358_ = leanh::lean_ctor_get(v_a_2351_, 2);
        v_ref_2359_ = leanh::lean_ctor_get(v_a_2351_, 5);
        v___x_2360_ = leanh::lean_unsigned_to_nat(0);
        v___x_2361_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2360_);
        v___x_2362_ = leanh::lean_unsigned_to_nat(2);
        v___x_2363_ = l_Lean_Syntax_getArg(v_x_2350_, v___x_2362_);
        leanh::lean_dec(v_x_2350_);
        v___x_2364_ = 0;
        v___x_2365_ = l_Lean_SourceInfo_fromRef(v_ref_2359_, v___x_2364_);
        v___x_2366_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2367_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2368_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2358_);
        leanh::lean_inc(v_quotContext_2357_);
        v___x_2369_ =
            l_Lean_addMacroScope(v_quotContext_2357_, v___x_2368_, v_currMacroScope_2358_);
        v___x_2370_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8;
        leanh::lean_inc_n(v___x_2365_, 2);
        v___x_2371_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2371_, 0, v___x_2365_);
        leanh::lean_ctor_set(v___x_2371_, 1, v___x_2367_);
        leanh::lean_ctor_set(v___x_2371_, 2, v___x_2369_);
        leanh::lean_ctor_set(v___x_2371_, 3, v___x_2370_);
        v___x_2372_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2373_ = l_Lean_Syntax_node2(v___x_2365_, v___x_2372_, v___x_2361_, v___x_2363_);
        v___x_2374_ = l_Lean_Syntax_node2(v___x_2365_, v___x_2366_, v___x_2371_, v___x_2373_);
        v___x_2375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2375_, 0, v___x_2374_);
        leanh::lean_ctor_set(v___x_2375_, 1, v_a_2352_);
        return v___x_2375_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1___boxed(
    mut v_x_2376_: *mut leanh::LeanObject,
    mut v_a_2377_: *mut leanh::LeanObject,
    mut v_a_2378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2379_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(v_x_2376_, v_a_2377_, v_a_2378_);
    leanh::lean_dec_ref(v_a_2377_);
    return v_res_2379_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0;
    v___x_2382_ = l_String_toRawSubstring_x27(v___x_2381_);
    return v___x_2382_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(
    mut v_x_2402_: *mut leanh::LeanObject,
    mut v_a_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    v___x_2405_ = l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1;
    leanh::lean_inc(v_x_2402_);
    v___x_2406_ = l_Lean_Syntax_isOfKind(v_x_2402_, v___x_2405_);
    if v___x_2406_ == 0 {
        let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2402_);
        v___x_2407_ = leanh::lean_box(1);
        v___x_2408_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2408_, 0, v___x_2407_);
        leanh::lean_ctor_set(v___x_2408_, 1, v_a_2404_);
        return v___x_2408_;
    } else {
        let mut v_quotContext_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: u8 = 0;
        let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2409_ = leanh::lean_ctor_get(v_a_2403_, 1);
        v_currMacroScope_2410_ = leanh::lean_ctor_get(v_a_2403_, 2);
        v_ref_2411_ = leanh::lean_ctor_get(v_a_2403_, 5);
        v___x_2412_ = leanh::lean_unsigned_to_nat(1);
        v___x_2413_ = l_Lean_Syntax_getArg(v_x_2402_, v___x_2412_);
        leanh::lean_dec(v_x_2402_);
        v___x_2414_ = 0;
        v___x_2415_ = l_Lean_SourceInfo_fromRef(v_ref_2411_, v___x_2414_);
        v___x_2416_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2417_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2418_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2410_);
        leanh::lean_inc(v_quotContext_2409_);
        v___x_2419_ =
            l_Lean_addMacroScope(v_quotContext_2409_, v___x_2418_, v_currMacroScope_2410_);
        v___x_2420_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8;
        leanh::lean_inc_n(v___x_2415_, 2);
        v___x_2421_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2421_, 0, v___x_2415_);
        leanh::lean_ctor_set(v___x_2421_, 1, v___x_2417_);
        leanh::lean_ctor_set(v___x_2421_, 2, v___x_2419_);
        leanh::lean_ctor_set(v___x_2421_, 3, v___x_2420_);
        v___x_2422_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2423_ = l_Lean_Syntax_node1(v___x_2415_, v___x_2422_, v___x_2413_);
        v___x_2424_ = l_Lean_Syntax_node2(v___x_2415_, v___x_2416_, v___x_2421_, v___x_2423_);
        v___x_2425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
        leanh::lean_ctor_set(v___x_2425_, 1, v_a_2404_);
        return v___x_2425_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___boxed(
    mut v_x_2426_: *mut leanh::LeanObject,
    mut v_a_2427_: *mut leanh::LeanObject,
    mut v_a_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(v_x_2426_, v_a_2427_, v_a_2428_);
    leanh::lean_dec_ref(v_a_2427_);
    return v_res_2429_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(
    mut v_x_2430_: *mut leanh::LeanObject,
    mut v_a_2431_: *mut leanh::LeanObject,
    mut v_a_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u8 = 0;
    v___x_2433_ = l_Std_term_x2a_x2e_x2e_x2e___00__closed__1;
    leanh::lean_inc(v_x_2430_);
    v___x_2434_ = l_Lean_Syntax_isOfKind(v_x_2430_, v___x_2433_);
    if v___x_2434_ == 0 {
        let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2430_);
        v___x_2435_ = leanh::lean_box(1);
        v___x_2436_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2436_, 0, v___x_2435_);
        leanh::lean_ctor_set(v___x_2436_, 1, v_a_2432_);
        return v___x_2436_;
    } else {
        let mut v_quotContext_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2442_: u8 = 0;
        let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2437_ = leanh::lean_ctor_get(v_a_2431_, 1);
        v_currMacroScope_2438_ = leanh::lean_ctor_get(v_a_2431_, 2);
        v_ref_2439_ = leanh::lean_ctor_get(v_a_2431_, 5);
        v___x_2440_ = leanh::lean_unsigned_to_nat(1);
        v___x_2441_ = l_Lean_Syntax_getArg(v_x_2430_, v___x_2440_);
        leanh::lean_dec(v_x_2430_);
        v___x_2442_ = 0;
        v___x_2443_ = l_Lean_SourceInfo_fromRef(v_ref_2439_, v___x_2442_);
        v___x_2444_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2445_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2446_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2438_);
        leanh::lean_inc(v_quotContext_2437_);
        v___x_2447_ =
            l_Lean_addMacroScope(v_quotContext_2437_, v___x_2446_, v_currMacroScope_2438_);
        v___x_2448_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8;
        leanh::lean_inc_n(v___x_2443_, 2);
        v___x_2449_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2449_, 0, v___x_2443_);
        leanh::lean_ctor_set(v___x_2449_, 1, v___x_2445_);
        leanh::lean_ctor_set(v___x_2449_, 2, v___x_2447_);
        leanh::lean_ctor_set(v___x_2449_, 3, v___x_2448_);
        v___x_2450_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2451_ = l_Lean_Syntax_node1(v___x_2443_, v___x_2450_, v___x_2441_);
        v___x_2452_ = l_Lean_Syntax_node2(v___x_2443_, v___x_2444_, v___x_2449_, v___x_2451_);
        v___x_2453_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2453_, 0, v___x_2452_);
        leanh::lean_ctor_set(v___x_2453_, 1, v_a_2432_);
        return v___x_2453_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1___boxed(
    mut v_x_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2457_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(v_x_2454_, v_a_2455_, v_a_2456_);
    leanh::lean_dec_ref(v_a_2455_);
    return v_res_2457_;
}
pub unsafe fn _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0;
    v___x_2460_ = l_String_toRawSubstring_x27(v___x_2459_);
    return v___x_2460_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(
    mut v_x_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
    mut v_a_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: u8 = 0;
    v___x_2483_ = l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1;
    leanh::lean_inc(v_x_2480_);
    v___x_2484_ = l_Lean_Syntax_isOfKind(v_x_2480_, v___x_2483_);
    if v___x_2484_ == 0 {
        let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2480_);
        v___x_2485_ = leanh::lean_box(1);
        v___x_2486_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2486_, 0, v___x_2485_);
        leanh::lean_ctor_set(v___x_2486_, 1, v_a_2482_);
        return v___x_2486_;
    } else {
        let mut v_quotContext_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: u8 = 0;
        let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2487_ = leanh::lean_ctor_get(v_a_2481_, 1);
        v_currMacroScope_2488_ = leanh::lean_ctor_get(v_a_2481_, 2);
        v_ref_2489_ = leanh::lean_ctor_get(v_a_2481_, 5);
        v___x_2490_ = leanh::lean_unsigned_to_nat(0);
        v___x_2491_ = l_Lean_Syntax_getArg(v_x_2480_, v___x_2490_);
        v___x_2492_ = leanh::lean_unsigned_to_nat(2);
        v___x_2493_ = l_Lean_Syntax_getArg(v_x_2480_, v___x_2492_);
        leanh::lean_dec(v_x_2480_);
        v___x_2494_ = 0;
        v___x_2495_ = l_Lean_SourceInfo_fromRef(v_ref_2489_, v___x_2494_);
        v___x_2496_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2497_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2498_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2488_);
        leanh::lean_inc(v_quotContext_2487_);
        v___x_2499_ =
            l_Lean_addMacroScope(v_quotContext_2487_, v___x_2498_, v_currMacroScope_2488_);
        v___x_2500_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8;
        leanh::lean_inc_n(v___x_2495_, 2);
        v___x_2501_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2501_, 0, v___x_2495_);
        leanh::lean_ctor_set(v___x_2501_, 1, v___x_2497_);
        leanh::lean_ctor_set(v___x_2501_, 2, v___x_2499_);
        leanh::lean_ctor_set(v___x_2501_, 3, v___x_2500_);
        v___x_2502_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2503_ = l_Lean_Syntax_node2(v___x_2495_, v___x_2502_, v___x_2491_, v___x_2493_);
        v___x_2504_ = l_Lean_Syntax_node2(v___x_2495_, v___x_2496_, v___x_2501_, v___x_2503_);
        v___x_2505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2505_, 0, v___x_2504_);
        leanh::lean_ctor_set(v___x_2505_, 1, v_a_2482_);
        return v___x_2505_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___boxed(
    mut v_x_2506_: *mut leanh::LeanObject,
    mut v_a_2507_: *mut leanh::LeanObject,
    mut v_a_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(v_x_2506_, v_a_2507_, v_a_2508_);
    leanh::lean_dec_ref(v_a_2507_);
    return v_res_2509_;
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(
    mut v_x_2510_: *mut leanh::LeanObject,
    mut v_a_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    v___x_2513_ = l_Std_term___x3c_x2e_x2e_x2e___00__closed__1;
    leanh::lean_inc(v_x_2510_);
    v___x_2514_ = l_Lean_Syntax_isOfKind(v_x_2510_, v___x_2513_);
    if v___x_2514_ == 0 {
        let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2510_);
        v___x_2515_ = leanh::lean_box(1);
        v___x_2516_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2516_, 0, v___x_2515_);
        leanh::lean_ctor_set(v___x_2516_, 1, v_a_2512_);
        return v___x_2516_;
    } else {
        let mut v_quotContext_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2524_: u8 = 0;
        let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2517_ = leanh::lean_ctor_get(v_a_2511_, 1);
        v_currMacroScope_2518_ = leanh::lean_ctor_get(v_a_2511_, 2);
        v_ref_2519_ = leanh::lean_ctor_get(v_a_2511_, 5);
        v___x_2520_ = leanh::lean_unsigned_to_nat(0);
        v___x_2521_ = l_Lean_Syntax_getArg(v_x_2510_, v___x_2520_);
        v___x_2522_ = leanh::lean_unsigned_to_nat(2);
        v___x_2523_ = l_Lean_Syntax_getArg(v_x_2510_, v___x_2522_);
        leanh::lean_dec(v_x_2510_);
        v___x_2524_ = 0;
        v___x_2525_ = l_Lean_SourceInfo_fromRef(v_ref_2519_, v___x_2524_);
        v___x_2526_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4;
        v___x_2527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1), core::ptr::addr_of_mut!(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once), _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
        v___x_2528_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3;
        leanh::lean_inc(v_currMacroScope_2518_);
        leanh::lean_inc(v_quotContext_2517_);
        v___x_2529_ =
            l_Lean_addMacroScope(v_quotContext_2517_, v___x_2528_, v_currMacroScope_2518_);
        v___x_2530_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8;
        leanh::lean_inc_n(v___x_2525_, 2);
        v___x_2531_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2531_, 0, v___x_2525_);
        leanh::lean_ctor_set(v___x_2531_, 1, v___x_2527_);
        leanh::lean_ctor_set(v___x_2531_, 2, v___x_2529_);
        leanh::lean_ctor_set(v___x_2531_, 3, v___x_2530_);
        v___x_2532_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16;
        v___x_2533_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2532_, v___x_2521_, v___x_2523_);
        v___x_2534_ = l_Lean_Syntax_node2(v___x_2525_, v___x_2526_, v___x_2531_, v___x_2533_);
        v___x_2535_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2535_, 0, v___x_2534_);
        leanh::lean_ctor_set(v___x_2535_, 1, v_a_2512_);
        return v___x_2535_;
    }
}
pub unsafe fn l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1___boxed(
    mut v_x_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(v_x_2536_, v_a_2537_, v_a_2538_);
    leanh::lean_dec_ref(v_a_2537_);
    return v_res_2539_;
}
pub unsafe fn l_Std_Rcc_instMembershipOfLE(
    mut v_00_u03b1_2540_: *mut leanh::LeanObject,
    mut v_inst_2541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = leanh::lean_box(0);
    return v___x_2542_;
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(
    mut v_r_2543_: *mut leanh::LeanObject,
    mut v_a_2544_: *mut leanh::LeanObject,
    mut v_inst_2545_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    v_lower_2546_ = leanh::lean_ctor_get(v_r_2543_, 0);
    leanh::lean_inc(v_lower_2546_);
    v_upper_2547_ = leanh::lean_ctor_get(v_r_2543_, 1);
    leanh::lean_inc(v_upper_2547_);
    leanh::lean_dec_ref(v_r_2543_);
    leanh::lean_inc_ref(v_inst_2545_);
    leanh::lean_inc(v_a_2544_);
    v___x_2548_ = leanh::lean_apply_2(v_inst_2545_, v_lower_2546_, v_a_2544_);
    v___x_2549_ = (leanh::lean_unbox(v___x_2548_) as u8);
    if v___x_2549_ == 0 {
        let mut v___x_2550_: u8 = 0;
        leanh::lean_dec(v_upper_2547_);
        leanh::lean_dec_ref(v_inst_2545_);
        leanh::lean_dec(v_a_2544_);
        v___x_2550_ = (leanh::lean_unbox(v___x_2548_) as u8);
        return v___x_2550_;
    } else {
        let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2552_: u8 = 0;
        v___x_2551_ = leanh::lean_apply_2(v_inst_2545_, v_a_2544_, v_upper_2547_);
        v___x_2552_ = (leanh::lean_unbox(v___x_2551_) as u8);
        return v___x_2552_;
    }
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(
    mut v_r_2553_: *mut leanh::LeanObject,
    mut v_a_2554_: *mut leanh::LeanObject,
    mut v_inst_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: u8 = 0;
    let mut v_r_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ =
        l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_2553_, v_a_2554_, v_inst_2555_);
    v_r_2557_ = leanh::lean_box((v_res_2556_) as usize);
    return v_r_2557_;
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE(
    mut v_00_u03b1_2558_: *mut leanh::LeanObject,
    mut v_r_2559_: *mut leanh::LeanObject,
    mut v_a_2560_: *mut leanh::LeanObject,
    mut v_inst_2561_: *mut leanh::LeanObject,
    mut v_inst_2562_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2563_: u8 = 0;
    v___x_2563_ =
        l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_2559_, v_a_2560_, v_inst_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(
    mut v_00_u03b1_2564_: *mut leanh::LeanObject,
    mut v_r_2565_: *mut leanh::LeanObject,
    mut v_a_2566_: *mut leanh::LeanObject,
    mut v_inst_2567_: *mut leanh::LeanObject,
    mut v_inst_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2569_: u8 = 0;
    let mut v_r_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Std_Rcc_instDecidableMemOfDecidableLE(
        v_00_u03b1_2564_,
        v_r_2565_,
        v_a_2566_,
        v_inst_2567_,
        v_inst_2568_,
    );
    v_r_2570_ = leanh::lean_box((v_res_2569_) as usize);
    return v_r_2570_;
}
pub unsafe fn l_Std_Rco_instMembershipOfLEOfLT(
    mut v_00_u03b1_2571_: *mut leanh::LeanObject,
    mut v_inst_2572_: *mut leanh::LeanObject,
    mut v_inst_2573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2574_ = leanh::lean_box(0);
    return v___x_2574_;
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
    mut v_r_2575_: *mut leanh::LeanObject,
    mut v_a_2576_: *mut leanh::LeanObject,
    mut v_inst_2577_: *mut leanh::LeanObject,
    mut v_inst_2578_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: u8 = 0;
    v_lower_2579_ = leanh::lean_ctor_get(v_r_2575_, 0);
    leanh::lean_inc(v_lower_2579_);
    v_upper_2580_ = leanh::lean_ctor_get(v_r_2575_, 1);
    leanh::lean_inc(v_upper_2580_);
    leanh::lean_dec_ref(v_r_2575_);
    leanh::lean_inc(v_a_2576_);
    v___x_2581_ = leanh::lean_apply_2(v_inst_2577_, v_lower_2579_, v_a_2576_);
    v___x_2582_ = (leanh::lean_unbox(v___x_2581_) as u8);
    if v___x_2582_ == 0 {
        let mut v___x_2583_: u8 = 0;
        leanh::lean_dec(v_upper_2580_);
        leanh::lean_dec_ref(v_inst_2578_);
        leanh::lean_dec(v_a_2576_);
        v___x_2583_ = (leanh::lean_unbox(v___x_2581_) as u8);
        return v___x_2583_;
    } else {
        let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2585_: u8 = 0;
        v___x_2584_ = leanh::lean_apply_2(v_inst_2578_, v_a_2576_, v_upper_2580_);
        v___x_2585_ = (leanh::lean_unbox(v___x_2584_) as u8);
        return v___x_2585_;
    }
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(
    mut v_r_2586_: *mut leanh::LeanObject,
    mut v_a_2587_: *mut leanh::LeanObject,
    mut v_inst_2588_: *mut leanh::LeanObject,
    mut v_inst_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2590_: u8 = 0;
    let mut v_r_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
        v_r_2586_,
        v_a_2587_,
        v_inst_2588_,
        v_inst_2589_,
    );
    v_r_2591_ = leanh::lean_box((v_res_2590_) as usize);
    return v_r_2591_;
}
pub unsafe fn l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(
    mut v_00_u03b1_2592_: *mut leanh::LeanObject,
    mut v_r_2593_: *mut leanh::LeanObject,
    mut v_a_2594_: *mut leanh::LeanObject,
    mut v_inst_2595_: *mut leanh::LeanObject,
    mut v_inst_2596_: *mut leanh::LeanObject,
    mut v_inst_2597_: *mut leanh::LeanObject,
    mut v_inst_2598_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_2600_: *mut leanh::LeanObject,
    mut v_r_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
    mut v_inst_2603_: *mut leanh::LeanObject,
    mut v_inst_2604_: *mut leanh::LeanObject,
    mut v_inst_2605_: *mut leanh::LeanObject,
    mut v_inst_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2607_: u8 = 0;
    let mut v_r_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(
        v_00_u03b1_2600_,
        v_r_2601_,
        v_a_2602_,
        v_inst_2603_,
        v_inst_2604_,
        v_inst_2605_,
        v_inst_2606_,
    );
    v_r_2608_ = leanh::lean_box((v_res_2607_) as usize);
    return v_r_2608_;
}
pub unsafe fn l_Std_Rci_instMembershipOfLE(
    mut v_00_u03b1_2609_: *mut leanh::LeanObject,
    mut v_inst_2610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2611_ = leanh::lean_box(0);
    return v___x_2611_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE___redArg(
    mut v_r_2612_: *mut leanh::LeanObject,
    mut v_a_2613_: *mut leanh::LeanObject,
    mut v_inst_2614_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: u8 = 0;
    v___x_2615_ = leanh::lean_apply_2(v_inst_2614_, v_r_2612_, v_a_2613_);
    v___x_2616_ = (leanh::lean_unbox(v___x_2615_) as u8);
    return v___x_2616_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(
    mut v_r_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_inst_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2620_: u8 = 0;
    let mut v_r_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ =
        l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_2617_, v_a_2618_, v_inst_2619_);
    v_r_2621_ = leanh::lean_box((v_res_2620_) as usize);
    return v_r_2621_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE(
    mut v_00_u03b1_2622_: *mut leanh::LeanObject,
    mut v_r_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
    mut v_inst_2625_: *mut leanh::LeanObject,
    mut v_inst_2626_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    v___x_2627_ = leanh::lean_apply_2(v_inst_2626_, v_r_2623_, v_a_2624_);
    v___x_2628_ = (leanh::lean_unbox(v___x_2627_) as u8);
    return v___x_2628_;
}
pub unsafe fn l_Std_Rci_instDecidableMemOfDecidableLE___boxed(
    mut v_00_u03b1_2629_: *mut leanh::LeanObject,
    mut v_r_2630_: *mut leanh::LeanObject,
    mut v_a_2631_: *mut leanh::LeanObject,
    mut v_inst_2632_: *mut leanh::LeanObject,
    mut v_inst_2633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2634_: u8 = 0;
    let mut v_r_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2634_ = l_Std_Rci_instDecidableMemOfDecidableLE(
        v_00_u03b1_2629_,
        v_r_2630_,
        v_a_2631_,
        v_inst_2632_,
        v_inst_2633_,
    );
    v_r_2635_ = leanh::lean_box((v_res_2634_) as usize);
    return v_r_2635_;
}
pub unsafe fn l_Std_Roc_instMembershipOfLEOfLT(
    mut v_00_u03b1_2636_: *mut leanh::LeanObject,
    mut v_inst_2637_: *mut leanh::LeanObject,
    mut v_inst_2638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = leanh::lean_box(0);
    return v___x_2639_;
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
    mut v_r_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_inst_2642_: *mut leanh::LeanObject,
    mut v_inst_2643_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    v_lower_2644_ = leanh::lean_ctor_get(v_r_2640_, 0);
    leanh::lean_inc(v_lower_2644_);
    v_upper_2645_ = leanh::lean_ctor_get(v_r_2640_, 1);
    leanh::lean_inc(v_upper_2645_);
    leanh::lean_dec_ref(v_r_2640_);
    leanh::lean_inc(v_a_2641_);
    v___x_2646_ = leanh::lean_apply_2(v_inst_2643_, v_lower_2644_, v_a_2641_);
    v___x_2647_ = (leanh::lean_unbox(v___x_2646_) as u8);
    if v___x_2647_ == 0 {
        let mut v___x_2648_: u8 = 0;
        leanh::lean_dec(v_upper_2645_);
        leanh::lean_dec_ref(v_inst_2642_);
        leanh::lean_dec(v_a_2641_);
        v___x_2648_ = (leanh::lean_unbox(v___x_2646_) as u8);
        return v___x_2648_;
    } else {
        let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2650_: u8 = 0;
        v___x_2649_ = leanh::lean_apply_2(v_inst_2642_, v_a_2641_, v_upper_2645_);
        v___x_2650_ = (leanh::lean_unbox(v___x_2649_) as u8);
        return v___x_2650_;
    }
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(
    mut v_r_2651_: *mut leanh::LeanObject,
    mut v_a_2652_: *mut leanh::LeanObject,
    mut v_inst_2653_: *mut leanh::LeanObject,
    mut v_inst_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2655_: u8 = 0;
    let mut v_r_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(
        v_r_2651_,
        v_a_2652_,
        v_inst_2653_,
        v_inst_2654_,
    );
    v_r_2656_ = leanh::lean_box((v_res_2655_) as usize);
    return v_r_2656_;
}
pub unsafe fn l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(
    mut v_00_u03b1_2657_: *mut leanh::LeanObject,
    mut v_r_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
    mut v_inst_2660_: *mut leanh::LeanObject,
    mut v_inst_2661_: *mut leanh::LeanObject,
    mut v_inst_2662_: *mut leanh::LeanObject,
    mut v_inst_2663_: *mut leanh::LeanObject,
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
    mut v_00_u03b1_2665_: *mut leanh::LeanObject,
    mut v_r_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_inst_2668_: *mut leanh::LeanObject,
    mut v_inst_2669_: *mut leanh::LeanObject,
    mut v_inst_2670_: *mut leanh::LeanObject,
    mut v_inst_2671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2672_: u8 = 0;
    let mut v_r_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(
        v_00_u03b1_2665_,
        v_r_2666_,
        v_a_2667_,
        v_inst_2668_,
        v_inst_2669_,
        v_inst_2670_,
        v_inst_2671_,
    );
    v_r_2673_ = leanh::lean_box((v_res_2672_) as usize);
    return v_r_2673_;
}
pub unsafe fn l_Std_Roo_instMembershipOfLT(
    mut v_00_u03b1_2674_: *mut leanh::LeanObject,
    mut v_inst_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = leanh::lean_box(0);
    return v___x_2676_;
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT___redArg(
    mut v_r_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
    mut v_inst_2679_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lower_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    v_lower_2680_ = leanh::lean_ctor_get(v_r_2677_, 0);
    leanh::lean_inc(v_lower_2680_);
    v_upper_2681_ = leanh::lean_ctor_get(v_r_2677_, 1);
    leanh::lean_inc(v_upper_2681_);
    leanh::lean_dec_ref(v_r_2677_);
    leanh::lean_inc_ref(v_inst_2679_);
    leanh::lean_inc(v_a_2678_);
    v___x_2682_ = leanh::lean_apply_2(v_inst_2679_, v_lower_2680_, v_a_2678_);
    v___x_2683_ = (leanh::lean_unbox(v___x_2682_) as u8);
    if v___x_2683_ == 0 {
        let mut v___x_2684_: u8 = 0;
        leanh::lean_dec(v_upper_2681_);
        leanh::lean_dec_ref(v_inst_2679_);
        leanh::lean_dec(v_a_2678_);
        v___x_2684_ = (leanh::lean_unbox(v___x_2682_) as u8);
        return v___x_2684_;
    } else {
        let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2686_: u8 = 0;
        v___x_2685_ = leanh::lean_apply_2(v_inst_2679_, v_a_2678_, v_upper_2681_);
        v___x_2686_ = (leanh::lean_unbox(v___x_2685_) as u8);
        return v___x_2686_;
    }
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(
    mut v_r_2687_: *mut leanh::LeanObject,
    mut v_a_2688_: *mut leanh::LeanObject,
    mut v_inst_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2690_: u8 = 0;
    let mut v_r_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2690_ =
        l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_2687_, v_a_2688_, v_inst_2689_);
    v_r_2691_ = leanh::lean_box((v_res_2690_) as usize);
    return v_r_2691_;
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT(
    mut v_00_u03b1_2692_: *mut leanh::LeanObject,
    mut v_r_2693_: *mut leanh::LeanObject,
    mut v_a_2694_: *mut leanh::LeanObject,
    mut v_inst_2695_: *mut leanh::LeanObject,
    mut v_inst_2696_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2697_: u8 = 0;
    v___x_2697_ =
        l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_2693_, v_a_2694_, v_inst_2696_);
    return v___x_2697_;
}
pub unsafe fn l_Std_Roo_instDecidableMemOfDecidableLT___boxed(
    mut v_00_u03b1_2698_: *mut leanh::LeanObject,
    mut v_r_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_inst_2701_: *mut leanh::LeanObject,
    mut v_inst_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2703_: u8 = 0;
    let mut v_r_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Std_Roo_instDecidableMemOfDecidableLT(
        v_00_u03b1_2698_,
        v_r_2699_,
        v_a_2700_,
        v_inst_2701_,
        v_inst_2702_,
    );
    v_r_2704_ = leanh::lean_box((v_res_2703_) as usize);
    return v_r_2704_;
}
pub unsafe fn l_Std_Roi_instMembershipOfLT(
    mut v_00_u03b1_2705_: *mut leanh::LeanObject,
    mut v_inst_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = leanh::lean_box(0);
    return v___x_2707_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT___redArg(
    mut v_r_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
    mut v_inst_2710_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    v___x_2711_ = leanh::lean_apply_2(v_inst_2710_, v_r_2708_, v_a_2709_);
    v___x_2712_ = (leanh::lean_unbox(v___x_2711_) as u8);
    return v___x_2712_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(
    mut v_r_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_inst_2715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2716_: u8 = 0;
    let mut v_r_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2716_ =
        l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_2713_, v_a_2714_, v_inst_2715_);
    v_r_2717_ = leanh::lean_box((v_res_2716_) as usize);
    return v_r_2717_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT(
    mut v_00_u03b1_2718_: *mut leanh::LeanObject,
    mut v_r_2719_: *mut leanh::LeanObject,
    mut v_a_2720_: *mut leanh::LeanObject,
    mut v_inst_2721_: *mut leanh::LeanObject,
    mut v_inst_2722_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: u8 = 0;
    v___x_2723_ = leanh::lean_apply_2(v_inst_2722_, v_r_2719_, v_a_2720_);
    v___x_2724_ = (leanh::lean_unbox(v___x_2723_) as u8);
    return v___x_2724_;
}
pub unsafe fn l_Std_Roi_instDecidableMemOfDecidableLT___boxed(
    mut v_00_u03b1_2725_: *mut leanh::LeanObject,
    mut v_r_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_inst_2728_: *mut leanh::LeanObject,
    mut v_inst_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2730_: u8 = 0;
    let mut v_r_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l_Std_Roi_instDecidableMemOfDecidableLT(
        v_00_u03b1_2725_,
        v_r_2726_,
        v_a_2727_,
        v_inst_2728_,
        v_inst_2729_,
    );
    v_r_2731_ = leanh::lean_box((v_res_2730_) as usize);
    return v_r_2731_;
}
pub unsafe fn l_Std_Ric_instMembershipOfLE(
    mut v_00_u03b1_2732_: *mut leanh::LeanObject,
    mut v_inst_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = leanh::lean_box(0);
    return v___x_2734_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE___redArg(
    mut v_r_2735_: *mut leanh::LeanObject,
    mut v_a_2736_: *mut leanh::LeanObject,
    mut v_inst_2737_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    v___x_2738_ = leanh::lean_apply_2(v_inst_2737_, v_a_2736_, v_r_2735_);
    v___x_2739_ = (leanh::lean_unbox(v___x_2738_) as u8);
    return v___x_2739_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(
    mut v_r_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_inst_2742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2743_: u8 = 0;
    let mut v_r_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2743_ =
        l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_2740_, v_a_2741_, v_inst_2742_);
    v_r_2744_ = leanh::lean_box((v_res_2743_) as usize);
    return v_r_2744_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE(
    mut v_00_u03b1_2745_: *mut leanh::LeanObject,
    mut v_r_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
    mut v_inst_2748_: *mut leanh::LeanObject,
    mut v_inst_2749_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    v___x_2750_ = leanh::lean_apply_2(v_inst_2749_, v_a_2747_, v_r_2746_);
    v___x_2751_ = (leanh::lean_unbox(v___x_2750_) as u8);
    return v___x_2751_;
}
pub unsafe fn l_Std_Ric_instDecidableMemOfDecidableLE___boxed(
    mut v_00_u03b1_2752_: *mut leanh::LeanObject,
    mut v_r_2753_: *mut leanh::LeanObject,
    mut v_a_2754_: *mut leanh::LeanObject,
    mut v_inst_2755_: *mut leanh::LeanObject,
    mut v_inst_2756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2757_: u8 = 0;
    let mut v_r_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2757_ = l_Std_Ric_instDecidableMemOfDecidableLE(
        v_00_u03b1_2752_,
        v_r_2753_,
        v_a_2754_,
        v_inst_2755_,
        v_inst_2756_,
    );
    v_r_2758_ = leanh::lean_box((v_res_2757_) as usize);
    return v_r_2758_;
}
pub unsafe fn l_Std_Rio_instMembershipOfLT(
    mut v_00_u03b1_2759_: *mut leanh::LeanObject,
    mut v_inst_2760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = leanh::lean_box(0);
    return v___x_2761_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT___redArg(
    mut v_r_2762_: *mut leanh::LeanObject,
    mut v_a_2763_: *mut leanh::LeanObject,
    mut v_inst_2764_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    v___x_2765_ = leanh::lean_apply_2(v_inst_2764_, v_a_2763_, v_r_2762_);
    v___x_2766_ = (leanh::lean_unbox(v___x_2765_) as u8);
    return v___x_2766_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(
    mut v_r_2767_: *mut leanh::LeanObject,
    mut v_a_2768_: *mut leanh::LeanObject,
    mut v_inst_2769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2770_: u8 = 0;
    let mut v_r_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2770_ =
        l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_2767_, v_a_2768_, v_inst_2769_);
    v_r_2771_ = leanh::lean_box((v_res_2770_) as usize);
    return v_r_2771_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT(
    mut v_00_u03b1_2772_: *mut leanh::LeanObject,
    mut v_r_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_inst_2775_: *mut leanh::LeanObject,
    mut v_inst_2776_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    v___x_2777_ = leanh::lean_apply_2(v_inst_2776_, v_a_2774_, v_r_2773_);
    v___x_2778_ = (leanh::lean_unbox(v___x_2777_) as u8);
    return v___x_2778_;
}
pub unsafe fn l_Std_Rio_instDecidableMemOfDecidableLT___boxed(
    mut v_00_u03b1_2779_: *mut leanh::LeanObject,
    mut v_r_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_inst_2782_: *mut leanh::LeanObject,
    mut v_inst_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2784_: u8 = 0;
    let mut v_r_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2784_ = l_Std_Rio_instDecidableMemOfDecidableLT(
        v_00_u03b1_2779_,
        v_r_2780_,
        v_a_2781_,
        v_inst_2782_,
        v_inst_2783_,
    );
    v_r_2785_ = leanh::lean_box((v_res_2784_) as usize);
    return v_r_2785_;
}
pub unsafe fn l_Std_Rii_instMembership(
    mut v_00_u03b1_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = leanh::lean_box(0);
    return v___x_2787_;
}
pub unsafe fn l_Std_Rii_instDecidableMem(
    mut v_00_u03b1_2788_: *mut leanh::LeanObject,
    mut v_r_2789_: *mut leanh::LeanObject,
    mut v_a_2790_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2791_: u8 = 0;
    v___x_2791_ = 1;
    return v___x_2791_;
}
pub unsafe fn l_Std_Rii_instDecidableMem___boxed(
    mut v_00_u03b1_2792_: *mut leanh::LeanObject,
    mut v_r_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2795_: u8 = 0;
    let mut v_r_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2795_ = l_Std_Rii_instDecidableMem(v_00_u03b1_2792_, v_r_2793_, v_a_2794_);
    leanh::lean_dec(v_a_2794_);
    v_r_2796_ = leanh::lean_box((v_res_2795_) as usize);
    return v_r_2796_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_PRange(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_PRange(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_PRange(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_PRange(builtin);
}