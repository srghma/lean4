// Lean compiler output
// Module: Lake.DSL.Syntax
// Imports: Lake.DSL.DeclUtil
use crate::r#gen::Lake::DSL::DeclUtil::{
    initialize_Lake_DSL_DeclUtil, l_Lake_DSL_declValDo, l_Lake_DSL_identOrStr,
    l_Lake_DSL_optConfig, l_Lake_DSL_simpleBinder, runtime_initialize_Lake_DSL_DeclUtil,
};
pub static l_Lake_DSL_nameConst___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 97, 107, 101, 0],
    };
static mut l_Lake_DSL_nameConst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__1_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [68, 83, 76, 0],
    };
static mut l_Lake_DSL_nameConst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__2_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [110, 97, 109, 101, 67, 111, 110, 115, 116, 0],
    };
static mut l_Lake_DSL_nameConst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_nameConst___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_nameConst___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_nameConst___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12277407653222002017 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_nameConst___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [95, 95, 110, 97, 109, 101, 95, 95, 0],
    };
static mut l_Lake_DSL_nameConst___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_nameConst___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_nameConst___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__6_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_nameConst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [100, 105, 114, 67, 111, 110, 115, 116, 0],
    };
static mut l_Lake_DSL_dirConst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_dirConst___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_dirConst___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_dirConst___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14737761738784435815 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_dirConst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [95, 95, 100, 105, 114, 95, 95, 0],
    };
static mut l_Lake_DSL_dirConst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_dirConst___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_dirConst___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_dirConst: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [103, 101, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_DSL_getConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_getConfig___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_getConfig___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_getConfig___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6629962664469725265 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__2_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lake_DSL_getConfig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12571085391447129896 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__4_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [103, 101, 116, 95, 99, 111, 110, 102, 105, 103, 63, 32, 0],
    };
static mut l_Lake_DSL_getConfig___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_getConfig___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__6_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lake_DSL_getConfig___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__6_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__7_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_getConfig___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__10_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_getConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_packageCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3605886163266385533 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18170484695678750185 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__4_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__4_value)
                as *mut crate::leanh::LeanObject,
            3961966953292576997 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__8_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__9_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__10_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__11_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_packageCommand___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageCommand___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageCommand___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageCommand___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__11_value)
                as *mut crate::leanh::LeanObject,
            2533412339571800130 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__16_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [112, 97, 99, 107, 97, 103, 101, 32, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__17_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_packageCommand___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_packageCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_instCoePackageCommandCommand___closed__0_value:
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
    m_fun: l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_DSL_instCoePackageCommandCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_instCoePackageCommandCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_postUpdateDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7248721378401769890 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [112, 111, 115, 116, 95, 117, 112, 100, 97, 116, 101, 32, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__5_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__5_value)
                as *mut crate::leanh::LeanObject,
            17761616517784022991 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_postUpdateDecl___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_postUpdateDecl___closed__11_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__11_value)
                as *mut crate::leanh::LeanObject,
            393173242845875278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__13_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__14_value: crate::leanh::LeanStringObject<14> =
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
            100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__13_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_postUpdateDecl___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__14_value)
                as *mut crate::leanh::LeanObject,
            13585030837571646948 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_postUpdateDecl___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_postUpdateDecl: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_fromPath___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [102, 114, 111, 109, 80, 97, 116, 104, 0],
    };
static mut l_Lake_DSL_fromPath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_fromPath___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromPath___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromPath___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10954861864498947928 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_fromPath___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8609355255726335675 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_fromPath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [102, 114, 111, 109, 71, 105, 116, 0],
    };
static mut l_Lake_DSL_fromGit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_fromGit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromGit___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromGit___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8744503865935906362 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [103, 105, 116, 32, 0],
    };
static mut l_Lake_DSL_fromGit___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__2_value)
                as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__4_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__6_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [64, 0],
    };
static mut l_Lake_DSL_fromGit___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__6_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_fromGit___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__11_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [47, 0],
    };
static mut l_Lake_DSL_fromGit___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__11_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_fromGit___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_fromGit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromSource___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [102, 114, 111, 109, 83, 111, 117, 114, 99, 101, 0],
    };
static mut l_Lake_DSL_fromSource___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_fromSource___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromSource___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromSource___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10611690220945862380 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromSource___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromSource___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromSource___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromSource___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromSource___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_fromSource: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [102, 114, 111, 109, 67, 108, 97, 117, 115, 101, 0],
    };
static mut l_Lake_DSL_fromClause___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_fromClause___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromClause___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromClause___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value)
                as *mut crate::leanh::LeanObject,
            862063901515217772 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromClause___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 102, 114, 111, 109, 32, 0],
    };
static mut l_Lake_DSL_fromClause___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_fromClause___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromClause___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromClause___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_fromClause: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [119, 105, 116, 104, 67, 108, 97, 117, 115, 101, 0],
    };
static mut l_Lake_DSL_withClause___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_withClause___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_withClause___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_withClause___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15981276745742611006 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_withClause___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 119, 105, 116, 104, 32, 0],
    };
static mut l_Lake_DSL_withClause___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_withClause___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_withClause___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_withClause___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_withClause___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_withClause: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [118, 101, 114, 83, 112, 101, 99, 0],
    };
static mut l_Lake_DSL_verSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_verSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_verSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_verSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3421776117942701061 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_verSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [118, 101, 114, 67, 108, 97, 117, 115, 101, 0],
    };
static mut l_Lake_DSL_verClause___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_verClause___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_verClause___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_verClause___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16691910745100808827 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verClause___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__2_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 64, 32, 0],
    };
static mut l_Lake_DSL_verClause___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_verClause___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_verClause___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verClause___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verClause___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_verClause: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 112, 78, 97, 109, 101, 0],
    };
static mut l_Lake_DSL_depName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_depName___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_depName___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_depName___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13377777968340814859 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lake_DSL_depName___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__2_value)
                as *mut crate::leanh::LeanObject,
            4024150434455327032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__4_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lake_DSL_depName___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__4_value)
                as *mut crate::leanh::LeanObject,
            9232979286016572671 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_depName___closed__5_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_depName___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__7_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [32, 47, 32, 0],
    };
static mut l_Lake_DSL_depName___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_depName___closed__7_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_depName___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_depName___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depName___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_depName___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depName___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_depName: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 112, 83, 112, 101, 99, 0],
    };
static mut l_Lake_DSL_depSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_depSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_depSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_depSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            142218530785266487 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_depSpec___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_depSpec___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_depSpec___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_depSpec___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_depSpec___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_depSpec: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_requireDecl___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [114, 101, 113, 117, 105, 114, 101, 68, 101, 99, 108, 0],
    };
static mut l_Lake_DSL_requireDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_requireDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_requireDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_requireDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2294773639995807415 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_requireDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_requireDecl___closed__2_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [114, 101, 113, 117, 105, 114, 101, 32, 0],
    };
static mut l_Lake_DSL_requireDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_requireDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_requireDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_requireDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_requireDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_requireDecl___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_requireDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_requireDecl___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_requireDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_requireDecl: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeRequireDeclCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_buildDeclSig___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [98, 117, 105, 108, 100, 68, 101, 99, 108, 83, 105, 103, 0],
    };
static mut l_Lake_DSL_buildDeclSig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_buildDeclSig___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_buildDeclSig___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_buildDeclSig___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14011375021470499909 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_buildDeclSig___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_buildDeclSig___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_buildDeclSig___closed__3_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0],
    };
static mut l_Lake_DSL_buildDeclSig___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_buildDeclSig___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            4498178684837002829 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_buildDeclSig___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_buildDeclSig___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_buildDeclSig___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_buildDeclSig___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_buildDeclSig___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_buildDeclSig___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_buildDeclSig: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_moduleFacetDecl___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            109, 111, 100, 117, 108, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_moduleFacetDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11101858149492730672 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__2_value: crate::leanh::LeanStringObject<14> =
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
            109, 111, 100, 117, 108, 101, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_moduleFacetDecl___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_moduleFacetDecl___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_moduleFacetDecl: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_packageFacetDecl___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            112, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageFacetDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7094079308183198759 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__2_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_packageFacetDecl___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageFacetDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageFacetDecl___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageFacetDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_packageFacetDecl: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_libraryFacetDecl___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            108, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_libraryFacetDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12396503196187142467 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__2_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            108, 105, 98, 114, 97, 114, 121, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_libraryFacetDecl___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_libraryFacetDecl___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_libraryFacetDecl: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_targetCommand___closed__0_value: crate::leanh::LeanStringObject<14> =
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
            116, 97, 114, 103, 101, 116, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_targetCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_targetCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_targetCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13148943219030950965 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_targetCommand___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [116, 97, 114, 103, 101, 116, 32, 0],
    };
static mut l_Lake_DSL_targetCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_targetCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_targetCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_targetCommand___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_targetCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_targetCommand___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_targetCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_targetCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_leanLibCommand___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            108, 101, 97, 110, 76, 105, 98, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_leanLibCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_leanLibCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_leanLibCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11637615818822604122 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__2_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 108, 105, 98, 32, 0],
    };
static mut l_Lake_DSL_leanLibCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_leanLibCommand___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanLibCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanLibCommand___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanLibCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanLibCommand___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanLibCommand___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_leanLibCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeLeanLibCommandCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            108, 101, 97, 110, 69, 120, 101, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_leanExeCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_leanExeCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_leanExeCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2062700356019151327 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__2_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 101, 120, 101, 32, 0],
    };
static mut l_Lake_DSL_leanExeCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_leanExeCommand___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanExeCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanExeCommand___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanExeCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanExeCommand___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanExeCommand___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_leanExeCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeLeanExeCommandCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            105, 110, 112, 117, 116, 70, 105, 108, 101, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_inputFileCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_inputFileCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_inputFileCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10121707264994059151 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__2_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [105, 110, 112, 117, 116, 95, 102, 105, 108, 101, 32, 0],
    };
static mut l_Lake_DSL_inputFileCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_inputFileCommand___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputFileCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputFileCommand___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputFileCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputFileCommand___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputFileCommand___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_inputFileCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeInputFileCommandCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 112, 117, 116, 68, 105, 114, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_inputDirCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_inputDirCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_inputDirCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8119030422813828009 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__2_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 32, 0],
    };
static mut l_Lake_DSL_inputDirCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_inputDirCommand___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputDirCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputDirCommand___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputDirCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputDirCommand___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputDirCommand___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_inputDirCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeInputDirCommandCommand: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_externLibDeclSpec___closed__0_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            101, 120, 116, 101, 114, 110, 76, 105, 98, 68, 101, 99, 108, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_externLibDeclSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12740147664822022041 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_externLibDeclSpec___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_externLibDeclSpec___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_externLibDeclSpec: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_externLibCommand___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            101, 120, 116, 101, 114, 110, 76, 105, 98, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_externLibCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_externLibCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_externLibCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9360286785500177995 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__2_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [101, 120, 116, 101, 114, 110, 95, 108, 105, 98, 32, 0],
    };
static mut l_Lake_DSL_externLibCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_externLibCommand___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibCommand___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_externLibCommand___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibCommand___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_externLibCommand: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_scriptDeclSpec___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_scriptDeclSpec___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7959617833543045482 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_scriptDeclSpec___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_scriptDeclSpec___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_scriptDeclSpec: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_scriptDecl___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 0],
    };
static mut l_Lake_DSL_scriptDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_scriptDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_scriptDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_scriptDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11447824861308129923 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_scriptDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [115, 99, 114, 105, 112, 116, 32, 0],
    };
static mut l_Lake_DSL_scriptDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_scriptDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_scriptDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_scriptDecl___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDecl___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_scriptDecl___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDecl___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_scriptDecl: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_verLit___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [118, 101, 114, 76, 105, 116, 0],
    };
static mut l_Lake_DSL_verLit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_verLit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_verLit___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_verLit___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9704141730406518167 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [118, 33, 0],
    };
static mut l_Lake_DSL_verLit___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_verLit___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_verLit___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_Lake_DSL_verLit___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__4_value)
                as *mut crate::leanh::LeanObject,
            1581446985683836252 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_verLit___closed__5_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_verLit___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__8_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
        ],
    };
static mut l_Lake_DSL_verLit___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__8_value)
                as *mut crate::leanh::LeanObject,
            18163029821153688220 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__12_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_verLit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__0_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [102, 97, 99, 101, 116, 83, 117, 102, 102, 105, 120, 0],
    };
static mut l_Lake_DSL_facetSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_facetSuffix___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_facetSuffix___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_facetSuffix___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7856869693164098343 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lake_DSL_facetSuffix___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_facetSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 76, 105, 116, 0,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_packageTargetLit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageTargetLit___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageTargetLit___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6142289428472292793 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [43, 0],
    };
static mut l_Lake_DSL_packageTargetLit___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_packageTargetLit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            109, 111, 100, 117, 108, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_moduleTargetKeyLit___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4666197752279438947 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [96, 43, 0],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__6_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
            2302572775315350313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_moduleTargetKeyLit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116,
            0,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageTargetKeyLit___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17001465581052579529 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [96, 64, 0],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_packageTargetKeyLit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 109, 100, 68, 111, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_cmdDo___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_cmdDo___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_cmdDo___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4812447225742894945 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2214559063752339918 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__4_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [100, 111, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_cmdDo___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__6_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [109, 97, 110, 121, 49, 73, 110, 100, 101, 110, 116, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__6_value)
                as *mut crate::leanh::LeanObject,
            16727513630015613089 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__8_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__8_value)
                as *mut crate::leanh::LeanObject,
            5063646790596052253 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_cmdDo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 101, 116, 97, 73, 102, 0],
    };
static mut l_Lake_DSL_metaIf___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_metaIf___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_metaIf___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_metaIf___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14561490878273970730 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__2_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [109, 101, 116, 97, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__4_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [105, 102, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__4_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__8_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 116, 104, 101, 110, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__8_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__10_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__12_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [32, 101, 108, 115, 101, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__12_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__16_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__17_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__17_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_metaIf: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [114, 117, 110, 73, 79, 0],
    };
static mut l_Lake_DSL_runIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_runIO___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_DSL_runIO___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut crate::leanh::LeanObject,
            5901868804703194544 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_runIO___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__0_value)
                as *mut crate::leanh::LeanObject,
            891786894088060352 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__2_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [114, 117, 110, 95, 105, 111, 32, 0],
    };
static mut l_Lake_DSL_runIO___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_runIO___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_runIO___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__4_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 111, 83, 101, 113, 0],
    };
static mut l_Lake_DSL_runIO___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__4_value)
                as *mut crate::leanh::LeanObject,
            12922580977142754391 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_runIO___closed__5_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_DSL_runIO___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__8_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_DSL_runIO: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__8_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lake_DSL_identOrStr;
    v___x_1068_ = l_Lake_DSL_packageCommand___closed__3;
    v___x_1069_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    crate::leanh::lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    return v___x_1069_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1071_ = l_Lake_DSL_packageCommand___closed__18;
    v___x_1072_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1073_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1073_, 0, v___x_1072_);
    crate::leanh::lean_ctor_set(v___x_1073_, 1, v___x_1071_);
    crate::leanh::lean_ctor_set(v___x_1073_, 2, v___x_1070_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = l_Lake_DSL_optConfig;
    v___x_1075_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__20),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__20_once),
        _init_l_Lake_DSL_packageCommand___closed__20,
    );
    v___x_1076_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1077_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_1076_);
    crate::leanh::lean_ctor_set(v___x_1077_, 1, v___x_1075_);
    crate::leanh::lean_ctor_set(v___x_1077_, 2, v___x_1074_);
    return v___x_1077_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__21),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__21_once),
        _init_l_Lake_DSL_packageCommand___closed__21,
    );
    v___x_1079_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1080_ = l_Lake_DSL_packageCommand___closed__1;
    v___x_1081_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_1080_);
    crate::leanh::lean_ctor_set(v___x_1081_, 1, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 2, v___x_1078_);
    return v___x_1081_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__22),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__22_once),
        _init_l_Lake_DSL_packageCommand___closed__22,
    );
    return v___x_1082_;
}
pub unsafe fn l_Lake_DSL_instCoePackageCommandCommand___lam__0(
    mut v_x_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1083_);
    return v_x_1083_;
}
pub unsafe fn l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed(
    mut v_x_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1085_ = l_Lake_DSL_instCoePackageCommandCommand___lam__0(v_x_1084_);
    crate::leanh::lean_dec(v_x_1084_);
    return v_res_1085_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lake_DSL_simpleBinder;
    v___x_1106_ = l_Lake_DSL_postUpdateDecl___closed__7;
    v___x_1107_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1108_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1108_, 1, v___x_1106_);
    crate::leanh::lean_ctor_set(v___x_1108_, 2, v___x_1105_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__8_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__8,
    );
    v___x_1110_ = l_Lake_DSL_packageCommand___closed__3;
    v___x_1111_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    crate::leanh::lean_ctor_set(v___x_1111_, 1, v___x_1109_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__9,
    );
    v___x_1113_ = l_Lake_DSL_postUpdateDecl___closed__4;
    v___x_1114_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1115_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1115_, 0, v___x_1114_);
    crate::leanh::lean_ctor_set(v___x_1115_, 1, v___x_1113_);
    crate::leanh::lean_ctor_set(v___x_1115_, 2, v___x_1112_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lake_DSL_declValDo;
    v___x_1129_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1130_ = l_Lake_DSL_postUpdateDecl___closed__12;
    v___x_1131_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    crate::leanh::lean_ctor_set(v___x_1131_, 1, v___x_1129_);
    crate::leanh::lean_ctor_set(v___x_1131_, 2, v___x_1128_);
    return v___x_1131_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__17,
    );
    v___x_1133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__10),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__10_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__10,
    );
    v___x_1134_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1135_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1135_, 0, v___x_1134_);
    crate::leanh::lean_ctor_set(v___x_1135_, 1, v___x_1133_);
    crate::leanh::lean_ctor_set(v___x_1135_, 2, v___x_1132_);
    return v___x_1135_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__18),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__18_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__18,
    );
    v___x_1137_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1138_ = l_Lake_DSL_postUpdateDecl___closed__1;
    v___x_1139_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    crate::leanh::lean_ctor_set(v___x_1139_, 1, v___x_1137_);
    crate::leanh::lean_ctor_set(v___x_1139_, 2, v___x_1136_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl() -> *mut crate::leanh::LeanObject {
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__19_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__19,
    );
    return v___x_1140_;
}
pub unsafe fn _init_l_Lake_DSL_depName___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Lake_DSL_identOrStr;
    v___x_1315_ = l_Lake_DSL_depName___closed__11;
    v___x_1316_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1317_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1317_, 0, v___x_1316_);
    crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1315_);
    crate::leanh::lean_ctor_set(v___x_1317_, 2, v___x_1314_);
    return v___x_1317_;
}
pub unsafe fn _init_l_Lake_DSL_depName___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__12),
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__12_once),
        _init_l_Lake_DSL_depName___closed__12,
    );
    v___x_1319_ = l_Lake_DSL_depName___closed__1;
    v___x_1320_ = l_Lake_DSL_depName___closed__0;
    v___x_1321_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    crate::leanh::lean_ctor_set(v___x_1321_, 1, v___x_1319_);
    crate::leanh::lean_ctor_set(v___x_1321_, 2, v___x_1318_);
    return v___x_1321_;
}
pub unsafe fn _init_l_Lake_DSL_depName() -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__13),
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__13_once),
        _init_l_Lake_DSL_depName___closed__13,
    );
    return v___x_1322_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lake_DSL_depSpec___closed__2;
    v___x_1332_ = l_Lake_DSL_depName;
    v___x_1333_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1334_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1334_, 0, v___x_1333_);
    crate::leanh::lean_ctor_set(v___x_1334_, 1, v___x_1332_);
    crate::leanh::lean_ctor_set(v___x_1334_, 2, v___x_1331_);
    return v___x_1334_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = l_Lake_DSL_depSpec___closed__4;
    v___x_1339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__3_once),
        _init_l_Lake_DSL_depSpec___closed__3,
    );
    v___x_1340_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1341_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1341_, 0, v___x_1340_);
    crate::leanh::lean_ctor_set(v___x_1341_, 1, v___x_1339_);
    crate::leanh::lean_ctor_set(v___x_1341_, 2, v___x_1338_);
    return v___x_1341_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lake_DSL_depSpec___closed__6;
    v___x_1346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__5_once),
        _init_l_Lake_DSL_depSpec___closed__5,
    );
    v___x_1347_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1348_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1348_, 0, v___x_1347_);
    crate::leanh::lean_ctor_set(v___x_1348_, 1, v___x_1346_);
    crate::leanh::lean_ctor_set(v___x_1348_, 2, v___x_1345_);
    return v___x_1348_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__7_once),
        _init_l_Lake_DSL_depSpec___closed__7,
    );
    v___x_1350_ = l_Lake_DSL_depSpec___closed__1;
    v___x_1351_ = l_Lake_DSL_depSpec___closed__0;
    v___x_1352_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
    crate::leanh::lean_ctor_set(v___x_1352_, 1, v___x_1350_);
    crate::leanh::lean_ctor_set(v___x_1352_, 2, v___x_1349_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec() -> *mut crate::leanh::LeanObject {
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__8_once),
        _init_l_Lake_DSL_depSpec___closed__8,
    );
    return v___x_1353_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lake_DSL_depSpec;
    v___x_1367_ = l_Lake_DSL_requireDecl___closed__4;
    v___x_1368_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1369_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    crate::leanh::lean_ctor_set(v___x_1369_, 1, v___x_1367_);
    crate::leanh::lean_ctor_set(v___x_1369_, 2, v___x_1366_);
    return v___x_1369_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__5_once),
        _init_l_Lake_DSL_requireDecl___closed__5,
    );
    v___x_1371_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1372_ = l_Lake_DSL_requireDecl___closed__1;
    v___x_1373_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1373_, 0, v___x_1372_);
    crate::leanh::lean_ctor_set(v___x_1373_, 1, v___x_1371_);
    crate::leanh::lean_ctor_set(v___x_1373_, 2, v___x_1370_);
    return v___x_1373_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl() -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__6_once),
        _init_l_Lake_DSL_requireDecl___closed__6,
    );
    return v___x_1374_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__9,
    );
    v___x_1382_ = l_Lake_DSL_identOrStr;
    v___x_1383_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1384_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1384_, 0, v___x_1383_);
    crate::leanh::lean_ctor_set(v___x_1384_, 1, v___x_1382_);
    crate::leanh::lean_ctor_set(v___x_1384_, 2, v___x_1381_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lake_DSL_buildDeclSig___closed__5;
    v___x_1394_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1395_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1396_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1396_, 0, v___x_1395_);
    crate::leanh::lean_ctor_set(v___x_1396_, 1, v___x_1394_);
    crate::leanh::lean_ctor_set(v___x_1396_, 2, v___x_1393_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__6_once),
        _init_l_Lake_DSL_buildDeclSig___closed__6,
    );
    v___x_1399_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1400_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1399_);
    crate::leanh::lean_ctor_set(v___x_1400_, 1, v___x_1398_);
    crate::leanh::lean_ctor_set(v___x_1400_, 2, v___x_1397_);
    return v___x_1400_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__7_once),
        _init_l_Lake_DSL_buildDeclSig___closed__7,
    );
    v___x_1402_ = l_Lake_DSL_buildDeclSig___closed__1;
    v___x_1403_ = l_Lake_DSL_buildDeclSig___closed__0;
    v___x_1404_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    crate::leanh::lean_ctor_set(v___x_1404_, 1, v___x_1402_);
    crate::leanh::lean_ctor_set(v___x_1404_, 2, v___x_1401_);
    return v___x_1404_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig() -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__8_once),
        _init_l_Lake_DSL_buildDeclSig___closed__8,
    );
    return v___x_1405_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1418_ = l_Lake_DSL_buildDeclSig;
    v___x_1419_ = l_Lake_DSL_moduleFacetDecl___closed__4;
    v___x_1420_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1421_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1421_, 0, v___x_1420_);
    crate::leanh::lean_ctor_set(v___x_1421_, 1, v___x_1419_);
    crate::leanh::lean_ctor_set(v___x_1421_, 2, v___x_1418_);
    return v___x_1421_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__5_once),
        _init_l_Lake_DSL_moduleFacetDecl___closed__5,
    );
    v___x_1423_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1424_ = l_Lake_DSL_moduleFacetDecl___closed__1;
    v___x_1425_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    crate::leanh::lean_ctor_set(v___x_1425_, 1, v___x_1423_);
    crate::leanh::lean_ctor_set(v___x_1425_, 2, v___x_1422_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl() -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__6_once),
        _init_l_Lake_DSL_moduleFacetDecl___closed__6,
    );
    return v___x_1426_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lake_DSL_buildDeclSig;
    v___x_1440_ = l_Lake_DSL_packageFacetDecl___closed__4;
    v___x_1441_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1442_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    crate::leanh::lean_ctor_set(v___x_1442_, 1, v___x_1440_);
    crate::leanh::lean_ctor_set(v___x_1442_, 2, v___x_1439_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__5_once),
        _init_l_Lake_DSL_packageFacetDecl___closed__5,
    );
    v___x_1444_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1445_ = l_Lake_DSL_packageFacetDecl___closed__1;
    v___x_1446_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    crate::leanh::lean_ctor_set(v___x_1446_, 1, v___x_1444_);
    crate::leanh::lean_ctor_set(v___x_1446_, 2, v___x_1443_);
    return v___x_1446_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl() -> *mut crate::leanh::LeanObject {
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__6_once),
        _init_l_Lake_DSL_packageFacetDecl___closed__6,
    );
    return v___x_1447_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Lake_DSL_buildDeclSig;
    v___x_1461_ = l_Lake_DSL_libraryFacetDecl___closed__4;
    v___x_1462_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1463_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1463_, 0, v___x_1462_);
    crate::leanh::lean_ctor_set(v___x_1463_, 1, v___x_1461_);
    crate::leanh::lean_ctor_set(v___x_1463_, 2, v___x_1460_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__5_once),
        _init_l_Lake_DSL_libraryFacetDecl___closed__5,
    );
    v___x_1465_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1466_ = l_Lake_DSL_libraryFacetDecl___closed__1;
    v___x_1467_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    crate::leanh::lean_ctor_set(v___x_1467_, 1, v___x_1465_);
    crate::leanh::lean_ctor_set(v___x_1467_, 2, v___x_1464_);
    return v___x_1467_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl() -> *mut crate::leanh::LeanObject {
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__6_once),
        _init_l_Lake_DSL_libraryFacetDecl___closed__6,
    );
    return v___x_1468_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lake_DSL_buildDeclSig;
    v___x_1482_ = l_Lake_DSL_targetCommand___closed__4;
    v___x_1483_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1484_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    crate::leanh::lean_ctor_set(v___x_1484_, 1, v___x_1482_);
    crate::leanh::lean_ctor_set(v___x_1484_, 2, v___x_1481_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__5_once),
        _init_l_Lake_DSL_targetCommand___closed__5,
    );
    v___x_1486_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1487_ = l_Lake_DSL_targetCommand___closed__1;
    v___x_1488_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
    crate::leanh::lean_ctor_set(v___x_1488_, 1, v___x_1486_);
    crate::leanh::lean_ctor_set(v___x_1488_, 2, v___x_1485_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__6_once),
        _init_l_Lake_DSL_targetCommand___closed__6,
    );
    return v___x_1489_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1503_ = l_Lake_DSL_leanLibCommand___closed__4;
    v___x_1504_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1505_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
    crate::leanh::lean_ctor_set(v___x_1505_, 1, v___x_1503_);
    crate::leanh::lean_ctor_set(v___x_1505_, 2, v___x_1502_);
    return v___x_1505_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = l_Lake_DSL_optConfig;
    v___x_1507_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__5_once),
        _init_l_Lake_DSL_leanLibCommand___closed__5,
    );
    v___x_1508_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1509_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    crate::leanh::lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    crate::leanh::lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__6_once),
        _init_l_Lake_DSL_leanLibCommand___closed__6,
    );
    v___x_1511_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1512_ = l_Lake_DSL_leanLibCommand___closed__1;
    v___x_1513_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    crate::leanh::lean_ctor_set(v___x_1513_, 2, v___x_1510_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__7_once),
        _init_l_Lake_DSL_leanLibCommand___closed__7,
    );
    return v___x_1514_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1529_ = l_Lake_DSL_leanExeCommand___closed__4;
    v___x_1530_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1531_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1529_);
    crate::leanh::lean_ctor_set(v___x_1531_, 2, v___x_1528_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Lake_DSL_optConfig;
    v___x_1533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__5_once),
        _init_l_Lake_DSL_leanExeCommand___closed__5,
    );
    v___x_1534_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1535_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    crate::leanh::lean_ctor_set(v___x_1535_, 1, v___x_1533_);
    crate::leanh::lean_ctor_set(v___x_1535_, 2, v___x_1532_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__6_once),
        _init_l_Lake_DSL_leanExeCommand___closed__6,
    );
    v___x_1537_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1538_ = l_Lake_DSL_leanExeCommand___closed__1;
    v___x_1539_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1539_, 0, v___x_1538_);
    crate::leanh::lean_ctor_set(v___x_1539_, 1, v___x_1537_);
    crate::leanh::lean_ctor_set(v___x_1539_, 2, v___x_1536_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__7_once),
        _init_l_Lake_DSL_leanExeCommand___closed__7,
    );
    return v___x_1540_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1555_ = l_Lake_DSL_inputFileCommand___closed__4;
    v___x_1556_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1557_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    crate::leanh::lean_ctor_set(v___x_1557_, 1, v___x_1555_);
    crate::leanh::lean_ctor_set(v___x_1557_, 2, v___x_1554_);
    return v___x_1557_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = l_Lake_DSL_optConfig;
    v___x_1559_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__5_once),
        _init_l_Lake_DSL_inputFileCommand___closed__5,
    );
    v___x_1560_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1561_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    crate::leanh::lean_ctor_set(v___x_1561_, 1, v___x_1559_);
    crate::leanh::lean_ctor_set(v___x_1561_, 2, v___x_1558_);
    return v___x_1561_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__6_once),
        _init_l_Lake_DSL_inputFileCommand___closed__6,
    );
    v___x_1563_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1564_ = l_Lake_DSL_inputFileCommand___closed__1;
    v___x_1565_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    crate::leanh::lean_ctor_set(v___x_1565_, 1, v___x_1563_);
    crate::leanh::lean_ctor_set(v___x_1565_, 2, v___x_1562_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__7_once),
        _init_l_Lake_DSL_inputFileCommand___closed__7,
    );
    return v___x_1566_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1581_ = l_Lake_DSL_inputDirCommand___closed__4;
    v___x_1582_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1583_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1582_);
    crate::leanh::lean_ctor_set(v___x_1583_, 1, v___x_1581_);
    crate::leanh::lean_ctor_set(v___x_1583_, 2, v___x_1580_);
    return v___x_1583_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lake_DSL_optConfig;
    v___x_1585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__5_once),
        _init_l_Lake_DSL_inputDirCommand___closed__5,
    );
    v___x_1586_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1587_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    crate::leanh::lean_ctor_set(v___x_1587_, 1, v___x_1585_);
    crate::leanh::lean_ctor_set(v___x_1587_, 2, v___x_1584_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__6_once),
        _init_l_Lake_DSL_inputDirCommand___closed__6,
    );
    v___x_1589_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1590_ = l_Lake_DSL_inputDirCommand___closed__1;
    v___x_1591_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1591_, 0, v___x_1590_);
    crate::leanh::lean_ctor_set(v___x_1591_, 1, v___x_1589_);
    crate::leanh::lean_ctor_set(v___x_1591_, 2, v___x_1588_);
    return v___x_1591_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__7_once),
        _init_l_Lake_DSL_inputDirCommand___closed__7,
    );
    return v___x_1592_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1600_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1601_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1602_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1602_, 0, v___x_1601_);
    crate::leanh::lean_ctor_set(v___x_1602_, 1, v___x_1600_);
    crate::leanh::lean_ctor_set(v___x_1602_, 2, v___x_1599_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__2_once),
        _init_l_Lake_DSL_externLibDeclSpec___closed__2,
    );
    v___x_1604_ = l_Lake_DSL_externLibDeclSpec___closed__1;
    v___x_1605_ = l_Lake_DSL_externLibDeclSpec___closed__0;
    v___x_1606_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1606_, 1, v___x_1604_);
    crate::leanh::lean_ctor_set(v___x_1606_, 2, v___x_1603_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec() -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__3_once),
        _init_l_Lake_DSL_externLibDeclSpec___closed__3,
    );
    return v___x_1607_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lake_DSL_externLibDeclSpec;
    v___x_1621_ = l_Lake_DSL_externLibCommand___closed__4;
    v___x_1622_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1623_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1623_, 0, v___x_1622_);
    crate::leanh::lean_ctor_set(v___x_1623_, 1, v___x_1621_);
    crate::leanh::lean_ctor_set(v___x_1623_, 2, v___x_1620_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__5_once),
        _init_l_Lake_DSL_externLibCommand___closed__5,
    );
    v___x_1625_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1626_ = l_Lake_DSL_externLibCommand___closed__1;
    v___x_1627_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1627_, 0, v___x_1626_);
    crate::leanh::lean_ctor_set(v___x_1627_, 1, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1627_, 2, v___x_1624_);
    return v___x_1627_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand() -> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__6_once),
        _init_l_Lake_DSL_externLibCommand___closed__6,
    );
    return v___x_1628_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__17,
    );
    v___x_1635_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1636_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1637_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1637_, 0, v___x_1636_);
    crate::leanh::lean_ctor_set(v___x_1637_, 1, v___x_1635_);
    crate::leanh::lean_ctor_set(v___x_1637_, 2, v___x_1634_);
    return v___x_1637_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__2_once),
        _init_l_Lake_DSL_scriptDeclSpec___closed__2,
    );
    v___x_1639_ = l_Lake_DSL_scriptDeclSpec___closed__1;
    v___x_1640_ = l_Lake_DSL_scriptDeclSpec___closed__0;
    v___x_1641_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1641_, 0, v___x_1640_);
    crate::leanh::lean_ctor_set(v___x_1641_, 1, v___x_1639_);
    crate::leanh::lean_ctor_set(v___x_1641_, 2, v___x_1638_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec() -> *mut crate::leanh::LeanObject {
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__3_once),
        _init_l_Lake_DSL_scriptDeclSpec___closed__3,
    );
    return v___x_1642_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lake_DSL_scriptDeclSpec;
    v___x_1656_ = l_Lake_DSL_scriptDecl___closed__4;
    v___x_1657_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1658_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1658_, 0, v___x_1657_);
    crate::leanh::lean_ctor_set(v___x_1658_, 1, v___x_1656_);
    crate::leanh::lean_ctor_set(v___x_1658_, 2, v___x_1655_);
    return v___x_1658_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__5_once),
        _init_l_Lake_DSL_scriptDecl___closed__5,
    );
    v___x_1660_ = crate::leanh::lean_unsigned_to_nat(1022);
    v___x_1661_ = l_Lake_DSL_scriptDecl___closed__1;
    v___x_1662_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    crate::leanh::lean_ctor_set(v___x_1662_, 1, v___x_1660_);
    crate::leanh::lean_ctor_set(v___x_1662_, 2, v___x_1659_);
    return v___x_1662_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl() -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__6_once),
        _init_l_Lake_DSL_scriptDecl___closed__6,
    );
    return v___x_1663_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_DSL_packageCommand = _init_l_Lake_DSL_packageCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_packageCommand);
    l_Lake_DSL_postUpdateDecl = _init_l_Lake_DSL_postUpdateDecl();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_postUpdateDecl);
    l_Lake_DSL_depName = _init_l_Lake_DSL_depName();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_depName);
    l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_depSpec);
    l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_requireDecl);
    l_Lake_DSL_buildDeclSig = _init_l_Lake_DSL_buildDeclSig();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_buildDeclSig);
    l_Lake_DSL_moduleFacetDecl = _init_l_Lake_DSL_moduleFacetDecl();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_moduleFacetDecl);
    l_Lake_DSL_packageFacetDecl = _init_l_Lake_DSL_packageFacetDecl();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_packageFacetDecl);
    l_Lake_DSL_libraryFacetDecl = _init_l_Lake_DSL_libraryFacetDecl();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_libraryFacetDecl);
    l_Lake_DSL_targetCommand = _init_l_Lake_DSL_targetCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_targetCommand);
    l_Lake_DSL_leanLibCommand = _init_l_Lake_DSL_leanLibCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_leanLibCommand);
    l_Lake_DSL_leanExeCommand = _init_l_Lake_DSL_leanExeCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_leanExeCommand);
    l_Lake_DSL_inputFileCommand = _init_l_Lake_DSL_inputFileCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_inputFileCommand);
    l_Lake_DSL_inputDirCommand = _init_l_Lake_DSL_inputDirCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_inputDirCommand);
    l_Lake_DSL_externLibDeclSpec = _init_l_Lake_DSL_externLibDeclSpec();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_externLibDeclSpec);
    l_Lake_DSL_externLibCommand = _init_l_Lake_DSL_externLibCommand();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_externLibCommand);
    l_Lake_DSL_scriptDeclSpec = _init_l_Lake_DSL_scriptDeclSpec();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_scriptDeclSpec);
    l_Lake_DSL_scriptDecl = _init_l_Lake_DSL_scriptDecl();
    crate::leanh::lean_mark_persistent(l_Lake_DSL_scriptDecl);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Syntax(builtin);
}
