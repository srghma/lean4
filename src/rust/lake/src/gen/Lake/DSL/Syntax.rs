// Lean compiler output
// Module: Lake.DSL.Syntax
// Imports: Lake.DSL.DeclUtil
use crate::r#gen::Lake::DSL::DeclUtil::{
    initialize_Lake_DSL_DeclUtil, l_Lake_DSL_declValDo, l_Lake_DSL_identOrStr,
    l_Lake_DSL_optConfig, l_Lake_DSL_simpleBinder, runtime_initialize_Lake_DSL_DeclUtil,
};
pub static l_Lake_DSL_nameConst___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 97, 107, 101, 0],
    };
static mut l_Lake_DSL_nameConst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__1_value: leanh::LeanStringObject<4> =
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
        m_data: [68, 83, 76, 0],
    };
static mut l_Lake_DSL_nameConst___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__2_value: leanh::LeanStringObject<10> =
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
        m_data: [110, 97, 109, 101, 67, 111, 110, 115, 116, 0],
    };
static mut l_Lake_DSL_nameConst___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__2_value) as *mut leanh::LeanObject;
static l_Lake_DSL_nameConst___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_nameConst___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_nameConst___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__2_value)
                as *mut leanh::LeanObject,
            12277407653222002017 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_nameConst___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__4_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_nameConst___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__4_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_nameConst___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_nameConst___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__3_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_nameConst___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__6_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_nameConst: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_dirConst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_dirConst___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_dirConst___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_dirConst___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__0_value)
                as *mut leanh::LeanObject,
            14737761738784435815 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_dirConst___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [95, 95, 100, 105, 114, 95, 95, 0],
    };
static mut l_Lake_DSL_dirConst___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_dirConst___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_dirConst___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_dirConst___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__4_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_dirConst: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_dirConst___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [103, 101, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lake_DSL_getConfig___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_getConfig___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_getConfig___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_getConfig___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__0_value)
                as *mut leanh::LeanObject,
            6629962664469725265 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__2_value: leanh::LeanStringObject<8> =
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
static mut l_Lake_DSL_getConfig___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__2_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__4_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_getConfig___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__4_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_getConfig___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__6_value: leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lake_DSL_getConfig___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__6_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__7_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_getConfig___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_getConfig___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_getConfig___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__10_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_getConfig: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_packageCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__0_value)
                as *mut leanh::LeanObject,
            3605886163266385533 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_packageCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__2_value)
                as *mut leanh::LeanObject,
            18170484695678750185 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__4_value: leanh::LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__4_value)
                as *mut leanh::LeanObject,
            3961966953292576997 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__8_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__9_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__10_value: leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__11_value: leanh::LeanStringObject<11> =
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
        m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
    };
static mut l_Lake_DSL_packageCommand___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_packageCommand___closed__12_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageCommand___closed__12_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageCommand___closed__12_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageCommand___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__11_value)
                as *mut leanh::LeanObject,
            2533412339571800130 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__16_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_packageCommand___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__17_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageCommand___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageCommand___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_packageCommand___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageCommand___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageCommand___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_packageCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_instCoePackageCommandCommand___closed__0_value:
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
    m_fun: l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_DSL_instCoePackageCommandCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_instCoePackageCommandCommand: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_postUpdateDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__0_value)
                as *mut leanh::LeanObject,
            7248721378401769890 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__2_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_postUpdateDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__5_value: leanh::LeanStringObject<8> =
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
        m_data: [112, 112, 83, 112, 97, 99, 101, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__5_value)
                as *mut leanh::LeanObject,
            17761616517784022991 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_postUpdateDecl___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_postUpdateDecl___closed__11_value: leanh::LeanStringObject<7> =
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
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__11_value)
                as *mut leanh::LeanObject,
            393173242845875278 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__13_value: leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__14_value: leanh::LeanStringObject<14> =
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
            100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__13_value)
                as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_postUpdateDecl___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__14_value)
                as *mut leanh::LeanObject,
            13585030837571646948 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_postUpdateDecl___closed__16_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_postUpdateDecl___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_postUpdateDecl___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_postUpdateDecl___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_postUpdateDecl___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_postUpdateDecl: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_fromPath___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_fromPath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_fromPath___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromPath___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromPath___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value)
                as *mut leanh::LeanObject,
            10954861864498947928 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__2_value: leanh::LeanStringObject<5> =
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
static mut l_Lake_DSL_fromPath___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__2_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromPath___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromPath___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_fromPath: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [102, 114, 111, 109, 71, 105, 116, 0],
    };
static mut l_Lake_DSL_fromGit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_fromGit___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromGit___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromGit___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value)
                as *mut leanh::LeanObject,
            8744503865935906362 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [103, 105, 116, 32, 0],
    };
static mut l_Lake_DSL_fromGit___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__2_value)
                as *mut leanh::LeanObject,
            0 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__3_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__6_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_fromGit___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__6_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_fromGit___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__11_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_fromGit___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__12_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__11_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_fromGit___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__13_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromGit___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromGit___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_fromGit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromSource___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [102, 114, 111, 109, 83, 111, 117, 114, 99, 101, 0],
    };
static mut l_Lake_DSL_fromSource___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_fromSource___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromSource___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromSource___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value)
                as *mut leanh::LeanObject,
            10611690220945862380 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromSource___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromSource___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromSource___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromSource___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromSource___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_fromSource: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [102, 114, 111, 109, 67, 108, 97, 117, 115, 101, 0],
    };
static mut l_Lake_DSL_fromClause___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_fromClause___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_fromClause___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_fromClause___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value)
                as *mut leanh::LeanObject,
            862063901515217772 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromClause___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 102, 114, 111, 109, 32, 0],
    };
static mut l_Lake_DSL_fromClause___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_fromClause___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromSource___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromClause___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_fromClause___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_fromClause___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_fromClause: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [119, 105, 116, 104, 67, 108, 97, 117, 115, 101, 0],
    };
static mut l_Lake_DSL_withClause___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_withClause___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_withClause___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_withClause___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value)
                as *mut leanh::LeanObject,
            15981276745742611006 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_withClause___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 119, 105, 116, 104, 32, 0],
    };
static mut l_Lake_DSL_withClause___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_withClause___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_withClause___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_withClause___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_withClause___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_withClause___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_withClause: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [118, 101, 114, 83, 112, 101, 99, 0],
    };
static mut l_Lake_DSL_verSpec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_verSpec___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_verSpec___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_verSpec___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value)
                as *mut leanh::LeanObject,
            3421776117942701061 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verSpec___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verSpec___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_verSpec: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [118, 101, 114, 67, 108, 97, 117, 115, 101, 0],
    };
static mut l_Lake_DSL_verClause___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_verClause___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_verClause___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_verClause___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value)
                as *mut leanh::LeanObject,
            16691910745100808827 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verClause___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__2_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 64, 32, 0],
    };
static mut l_Lake_DSL_verClause___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_verClause___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_verClause___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verSpec___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verClause___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verClause___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verClause___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_verClause: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 112, 78, 97, 109, 101, 0],
    };
static mut l_Lake_DSL_depName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_depName___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_depName___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_depName___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__0_value)
                as *mut leanh::LeanObject,
            13377777968340814859 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [97, 116, 111, 109, 105, 99, 0],
    };
static mut l_Lake_DSL_depName___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__2_value)
                as *mut leanh::LeanObject,
            4024150434455327032 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__4_value: leanh::LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lake_DSL_depName___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__4_value)
                as *mut leanh::LeanObject,
            9232979286016572671 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_depName___closed__5_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_depName___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__7_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 47, 32, 0],
    };
static mut l_Lake_DSL_depName___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_depName___closed__7_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_depName___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depName___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depName___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depName___closed__11_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_depName___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depName___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_depName___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depName___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_depName: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 112, 83, 112, 101, 99, 0],
    };
static mut l_Lake_DSL_depSpec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_depSpec___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_depSpec___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_depSpec___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__0_value)
                as *mut leanh::LeanObject,
            142218530785266487 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_depSpec___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verClause___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_depSpec___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromClause___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_depSpec___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_depSpec___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_withClause___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_depSpec___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_depSpec___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_depSpec___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_depSpec___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_depSpec___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_depSpec: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_requireDecl___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_requireDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_requireDecl___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_requireDecl___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_requireDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__0_value)
                as *mut leanh::LeanObject,
            2294773639995807415 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_requireDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_requireDecl___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_requireDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_requireDecl___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_requireDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_requireDecl___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_requireDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_requireDecl___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_requireDecl___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_requireDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_requireDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_requireDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_requireDecl: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeRequireDeclCommand: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_buildDeclSig___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_buildDeclSig___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_buildDeclSig___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_buildDeclSig___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_buildDeclSig___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__0_value)
                as *mut leanh::LeanObject,
            14011375021470499909 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_buildDeclSig___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_buildDeclSig___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_buildDeclSig___closed__3_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_buildDeclSig___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__3_value) as *mut leanh::LeanObject;
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__8_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__9_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_buildDeclSig___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__10_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_buildDeclSig___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__3_value)
                as *mut leanh::LeanObject,
            4498178684837002829 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_buildDeclSig___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_buildDeclSig___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 8,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_buildDeclSig___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_buildDeclSig___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_buildDeclSig___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_buildDeclSig___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_buildDeclSig___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_buildDeclSig___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_buildDeclSig: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_moduleFacetDecl___closed__0_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_moduleFacetDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_moduleFacetDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__0_value)
                as *mut leanh::LeanObject,
            11101858149492730672 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__2_value: leanh::LeanStringObject<14> =
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
            109, 111, 100, 117, 108, 101, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleFacetDecl___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleFacetDecl___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_moduleFacetDecl___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_moduleFacetDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_moduleFacetDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_moduleFacetDecl: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_packageFacetDecl___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageFacetDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__0_value)
                as *mut leanh::LeanObject,
            7094079308183198759 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__2_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageFacetDecl___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageFacetDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageFacetDecl___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_packageFacetDecl___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageFacetDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_packageFacetDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_packageFacetDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_packageFacetDecl: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_libraryFacetDecl___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
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
            108, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_libraryFacetDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__0_value)
                as *mut leanh::LeanObject,
            12396503196187142467 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__2_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            108, 105, 98, 114, 97, 114, 121, 95, 102, 97, 99, 101, 116, 32, 0,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_libraryFacetDecl___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_libraryFacetDecl___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_libraryFacetDecl___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_libraryFacetDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_libraryFacetDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_libraryFacetDecl: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_targetCommand___closed__0_value: leanh::LeanStringObject<14> =
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
            116, 97, 114, 103, 101, 116, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_targetCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_targetCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_targetCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__0_value)
                as *mut leanh::LeanObject,
            13148943219030950965 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_targetCommand___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 97, 114, 103, 101, 116, 32, 0],
    };
static mut l_Lake_DSL_targetCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_targetCommand___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_targetCommand___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_targetCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_targetCommand___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_targetCommand___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_targetCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_targetCommand___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_targetCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_targetCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_leanLibCommand___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            108, 101, 97, 110, 76, 105, 98, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_leanLibCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_leanLibCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_leanLibCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__0_value)
                as *mut leanh::LeanObject,
            11637615818822604122 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__2_value: leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 108, 105, 98, 32, 0],
    };
static mut l_Lake_DSL_leanLibCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanLibCommand___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanLibCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanLibCommand___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_leanLibCommand___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanLibCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanLibCommand___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanLibCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanLibCommand___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanLibCommand___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_leanLibCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeLeanLibCommandCommand: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            108, 101, 97, 110, 69, 120, 101, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_leanExeCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_leanExeCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_leanExeCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__0_value)
                as *mut leanh::LeanObject,
            2062700356019151327 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__2_value: leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 101, 120, 101, 32, 0],
    };
static mut l_Lake_DSL_leanExeCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_leanExeCommand___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_leanExeCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_leanExeCommand___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_leanExeCommand___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanExeCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanExeCommand___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanExeCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_leanExeCommand___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_leanExeCommand___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_leanExeCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeLeanExeCommandCommand: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
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
            105, 110, 112, 117, 116, 70, 105, 108, 101, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_inputFileCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_inputFileCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_inputFileCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__0_value)
                as *mut leanh::LeanObject,
            10121707264994059151 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__2_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_inputFileCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputFileCommand___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputFileCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputFileCommand___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_inputFileCommand___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputFileCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputFileCommand___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputFileCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputFileCommand___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputFileCommand___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_inputFileCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeInputFileCommandCommand: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__0_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_inputDirCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_inputDirCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_inputDirCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_inputDirCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__0_value)
                as *mut leanh::LeanObject,
            8119030422813828009 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__2_value: leanh::LeanStringObject<11> =
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
        m_data: [105, 110, 112, 117, 116, 95, 100, 105, 114, 32, 0],
    };
static mut l_Lake_DSL_inputDirCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_inputDirCommand___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_inputDirCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_inputDirCommand___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_inputDirCommand___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputDirCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputDirCommand___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputDirCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_inputDirCommand___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_inputDirCommand___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_inputDirCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_instCoeInputDirCommandCommand: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instCoePackageCommandCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_externLibDeclSpec___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_externLibDeclSpec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_externLibDeclSpec___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__0_value)
                as *mut leanh::LeanObject,
            12740147664822022041 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibDeclSpec___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_externLibDeclSpec___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_externLibDeclSpec___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibDeclSpec___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_externLibDeclSpec: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_externLibCommand___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
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
            101, 120, 116, 101, 114, 110, 76, 105, 98, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_externLibCommand___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_externLibCommand___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_externLibCommand___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__0_value)
                as *mut leanh::LeanObject,
            9360286785500177995 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__2_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_externLibCommand___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_externLibCommand___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_externLibCommand___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_externLibCommand___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_externLibCommand___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibCommand___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_externLibCommand___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_externLibCommand___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_externLibCommand: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_scriptDeclSpec___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_scriptDeclSpec___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__0_value)
                as *mut leanh::LeanObject,
            7959617833543045482 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDeclSpec___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_scriptDeclSpec___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_scriptDeclSpec___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDeclSpec___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_scriptDeclSpec: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_scriptDecl___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [115, 99, 114, 105, 112, 116, 68, 101, 99, 108, 0],
    };
static mut l_Lake_DSL_scriptDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_scriptDecl___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_scriptDecl___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_scriptDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__0_value)
                as *mut leanh::LeanObject,
            11447824861308129923 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_scriptDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [115, 99, 114, 105, 112, 116, 32, 0],
    };
static mut l_Lake_DSL_scriptDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_scriptDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_scriptDecl___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_scriptDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_scriptDecl___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_DSL_scriptDecl___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDecl___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_DSL_scriptDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_scriptDecl___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_DSL_scriptDecl: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_verLit___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [118, 101, 114, 76, 105, 116, 0],
    };
static mut l_Lake_DSL_verLit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_verLit___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_verLit___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_verLit___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__0_value)
                as *mut leanh::LeanObject,
            9704141730406518167 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [118, 33, 0],
    };
static mut l_Lake_DSL_verLit___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_verLit___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_verLit___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 87, 115, 0],
    };
static mut l_Lake_DSL_verLit___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__4_value)
                as *mut leanh::LeanObject,
            1581446985683836252 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_verLit___closed__5_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_verLit___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__8_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_verLit___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__8_value)
                as *mut leanh::LeanObject,
            18163029821153688220 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_verLit___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_verLit___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__12_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_verLit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_verLit___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_facetSuffix___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_facetSuffix___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_facetSuffix___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_facetSuffix___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value)
                as *mut leanh::LeanObject,
            7856869693164098343 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_facetSuffix___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_facetSuffix___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_facetSuffix___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_facetSuffix: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 76, 105, 116, 0,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_packageTargetLit___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageTargetLit___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageTargetLit___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value)
                as *mut leanh::LeanObject,
            6142289428472292793 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_packageTargetLit___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetLit___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetLit___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_packageTargetLit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__0_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
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
            109, 111, 100, 117, 108, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116, 0,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_moduleTargetKeyLit___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__0_value)
                as *mut leanh::LeanObject,
            4666197752279438947 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [96, 43, 0],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__6_value: leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 110, 121, 0],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__6_value)
                as *mut leanh::LeanObject,
            2302572775315350313 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_moduleTargetKeyLit___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_moduleTargetKeyLit___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__10_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_moduleTargetKeyLit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__0_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 84, 97, 114, 103, 101, 116, 75, 101, 121, 76, 105, 116,
            0,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_packageTargetKeyLit___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__0_value)
                as *mut leanh::LeanObject,
            17001465581052579529 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [96, 64, 0],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromGit___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_depName___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetLit___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__13_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_verLit___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_facetSuffix___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_moduleTargetKeyLit___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_packageTargetKeyLit___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__1_value)
                as *mut leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_packageTargetKeyLit___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__16_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_packageTargetKeyLit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_packageTargetKeyLit___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [99, 109, 100, 68, 111, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_cmdDo___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_cmdDo___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_cmdDo___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value)
                as *mut leanh::LeanObject,
            4812447225742894945 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [103, 114, 111, 117, 112, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__2_value)
                as *mut leanh::LeanObject,
            2214559063752339918 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__4_value: leanh::LeanStringObject<3> =
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
        m_data: [100, 111, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__4_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_cmdDo___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__6_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_cmdDo___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__6_value)
                as *mut leanh::LeanObject,
            16727513630015613089 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__8_value: leanh::LeanStringObject<8> =
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
        m_data: [99, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lake_DSL_cmdDo___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__8_value)
                as *mut leanh::LeanObject,
            5063646790596052253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__9_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_postUpdateDecl___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_cmdDo___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 9,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_cmdDo___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_cmdDo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [109, 101, 116, 97, 73, 102, 0],
    };
static mut l_Lake_DSL_metaIf___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_metaIf___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_metaIf___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_metaIf___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__0_value)
                as *mut leanh::LeanObject,
            14561490878273970730 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [109, 101, 116, 97, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__4_value: leanh::LeanStringObject<4> =
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
        m_data: [105, 102, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__4_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_fromPath___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__8_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 116, 104, 101, 110, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__8_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__12_value: leanh::LeanStringObject<7> =
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
        m_data: [32, 101, 108, 115, 101, 32, 0],
    };
static mut l_Lake_DSL_metaIf___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__12_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_metaIf___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_cmdDo___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_DSL_packageCommand___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_metaIf___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_metaIf___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__17_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_metaIf: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_metaIf___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [114, 117, 110, 73, 79, 0],
    };
static mut l_Lake_DSL_runIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__0_value) as *mut leanh::LeanObject;
static l_Lake_DSL_runIO___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
static l_Lake_DSL_runIO___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_nameConst___closed__1_value)
                as *mut leanh::LeanObject,
            5901868804703194544 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_runIO___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__0_value)
                as *mut leanh::LeanObject,
            891786894088060352 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [114, 117, 110, 95, 105, 111, 32, 0],
    };
static mut l_Lake_DSL_runIO___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_runIO___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_runIO___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__4_value: leanh::LeanStringObject<6> =
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
        m_data: [100, 111, 83, 101, 113, 0],
    };
static mut l_Lake_DSL_runIO___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__4_value)
                as *mut leanh::LeanObject,
            12922580977142754391 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_DSL_runIO___closed__5_value)
            as *mut leanh::LeanObject],
    };
static mut l_Lake_DSL_runIO___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_getConfig___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_DSL_runIO___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__1_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_runIO___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_runIO___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__8_value) as *mut leanh::LeanObject;
pub static mut l_Lake_DSL_runIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_runIO___closed__8_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lake_DSL_identOrStr;
    v___x_1068_ = l_Lake_DSL_packageCommand___closed__3;
    v___x_1069_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    leanh::lean_ctor_set(v___x_1069_, 1, v___x_1067_);
    return v___x_1069_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1071_ = l_Lake_DSL_packageCommand___closed__18;
    v___x_1072_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1073_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1073_, 0, v___x_1072_);
    leanh::lean_ctor_set(v___x_1073_, 1, v___x_1071_);
    leanh::lean_ctor_set(v___x_1073_, 2, v___x_1070_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = l_Lake_DSL_optConfig;
    v___x_1075_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__20),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__20_once),
        _init_l_Lake_DSL_packageCommand___closed__20,
    );
    v___x_1076_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1077_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1077_, 0, v___x_1076_);
    leanh::lean_ctor_set(v___x_1077_, 1, v___x_1075_);
    leanh::lean_ctor_set(v___x_1077_, 2, v___x_1074_);
    return v___x_1077_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__21),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__21_once),
        _init_l_Lake_DSL_packageCommand___closed__21,
    );
    v___x_1079_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1080_ = l_Lake_DSL_packageCommand___closed__1;
    v___x_1081_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1081_, 0, v___x_1080_);
    leanh::lean_ctor_set(v___x_1081_, 1, v___x_1079_);
    leanh::lean_ctor_set(v___x_1081_, 2, v___x_1078_);
    return v___x_1081_;
}
pub unsafe fn _init_l_Lake_DSL_packageCommand() -> *mut leanh::LeanObject {
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__22),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__22_once),
        _init_l_Lake_DSL_packageCommand___closed__22,
    );
    return v___x_1082_;
}
pub unsafe fn l_Lake_DSL_instCoePackageCommandCommand___lam__0(
    mut v_x_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_1083_);
    return v_x_1083_;
}
pub unsafe fn l_Lake_DSL_instCoePackageCommandCommand___lam__0___boxed(
    mut v_x_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1085_ = l_Lake_DSL_instCoePackageCommandCommand___lam__0(v_x_1084_);
    leanh::lean_dec(v_x_1084_);
    return v_res_1085_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lake_DSL_simpleBinder;
    v___x_1106_ = l_Lake_DSL_postUpdateDecl___closed__7;
    v___x_1107_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1108_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
    leanh::lean_ctor_set(v___x_1108_, 1, v___x_1106_);
    leanh::lean_ctor_set(v___x_1108_, 2, v___x_1105_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__8_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__8,
    );
    v___x_1110_ = l_Lake_DSL_packageCommand___closed__3;
    v___x_1111_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    leanh::lean_ctor_set(v___x_1111_, 1, v___x_1109_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__9,
    );
    v___x_1113_ = l_Lake_DSL_postUpdateDecl___closed__4;
    v___x_1114_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1115_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1115_, 0, v___x_1114_);
    leanh::lean_ctor_set(v___x_1115_, 1, v___x_1113_);
    leanh::lean_ctor_set(v___x_1115_, 2, v___x_1112_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lake_DSL_declValDo;
    v___x_1129_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1130_ = l_Lake_DSL_postUpdateDecl___closed__12;
    v___x_1131_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    leanh::lean_ctor_set(v___x_1131_, 1, v___x_1129_);
    leanh::lean_ctor_set(v___x_1131_, 2, v___x_1128_);
    return v___x_1131_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__17,
    );
    v___x_1133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__10),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__10_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__10,
    );
    v___x_1134_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1135_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1135_, 0, v___x_1134_);
    leanh::lean_ctor_set(v___x_1135_, 1, v___x_1133_);
    leanh::lean_ctor_set(v___x_1135_, 2, v___x_1132_);
    return v___x_1135_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__18),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__18_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__18,
    );
    v___x_1137_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1138_ = l_Lake_DSL_postUpdateDecl___closed__1;
    v___x_1139_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    leanh::lean_ctor_set(v___x_1139_, 1, v___x_1137_);
    leanh::lean_ctor_set(v___x_1139_, 2, v___x_1136_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lake_DSL_postUpdateDecl() -> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__19_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__19,
    );
    return v___x_1140_;
}
pub unsafe fn _init_l_Lake_DSL_depName___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Lake_DSL_identOrStr;
    v___x_1315_ = l_Lake_DSL_depName___closed__11;
    v___x_1316_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1317_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1317_, 0, v___x_1316_);
    leanh::lean_ctor_set(v___x_1317_, 1, v___x_1315_);
    leanh::lean_ctor_set(v___x_1317_, 2, v___x_1314_);
    return v___x_1317_;
}
pub unsafe fn _init_l_Lake_DSL_depName___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1318_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__12),
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__12_once),
        _init_l_Lake_DSL_depName___closed__12,
    );
    v___x_1319_ = l_Lake_DSL_depName___closed__1;
    v___x_1320_ = l_Lake_DSL_depName___closed__0;
    v___x_1321_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    leanh::lean_ctor_set(v___x_1321_, 1, v___x_1319_);
    leanh::lean_ctor_set(v___x_1321_, 2, v___x_1318_);
    return v___x_1321_;
}
pub unsafe fn _init_l_Lake_DSL_depName() -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__13),
        core::ptr::addr_of_mut!(l_Lake_DSL_depName___closed__13_once),
        _init_l_Lake_DSL_depName___closed__13,
    );
    return v___x_1322_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_Lake_DSL_depSpec___closed__2;
    v___x_1332_ = l_Lake_DSL_depName;
    v___x_1333_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1334_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1334_, 0, v___x_1333_);
    leanh::lean_ctor_set(v___x_1334_, 1, v___x_1332_);
    leanh::lean_ctor_set(v___x_1334_, 2, v___x_1331_);
    return v___x_1334_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = l_Lake_DSL_depSpec___closed__4;
    v___x_1339_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__3_once),
        _init_l_Lake_DSL_depSpec___closed__3,
    );
    v___x_1340_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1341_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1341_, 0, v___x_1340_);
    leanh::lean_ctor_set(v___x_1341_, 1, v___x_1339_);
    leanh::lean_ctor_set(v___x_1341_, 2, v___x_1338_);
    return v___x_1341_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l_Lake_DSL_depSpec___closed__6;
    v___x_1346_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__5_once),
        _init_l_Lake_DSL_depSpec___closed__5,
    );
    v___x_1347_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1348_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1348_, 0, v___x_1347_);
    leanh::lean_ctor_set(v___x_1348_, 1, v___x_1346_);
    leanh::lean_ctor_set(v___x_1348_, 2, v___x_1345_);
    return v___x_1348_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__7_once),
        _init_l_Lake_DSL_depSpec___closed__7,
    );
    v___x_1350_ = l_Lake_DSL_depSpec___closed__1;
    v___x_1351_ = l_Lake_DSL_depSpec___closed__0;
    v___x_1352_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1352_, 0, v___x_1351_);
    leanh::lean_ctor_set(v___x_1352_, 1, v___x_1350_);
    leanh::lean_ctor_set(v___x_1352_, 2, v___x_1349_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lake_DSL_depSpec() -> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_depSpec___closed__8_once),
        _init_l_Lake_DSL_depSpec___closed__8,
    );
    return v___x_1353_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lake_DSL_depSpec;
    v___x_1367_ = l_Lake_DSL_requireDecl___closed__4;
    v___x_1368_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1369_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    leanh::lean_ctor_set(v___x_1369_, 1, v___x_1367_);
    leanh::lean_ctor_set(v___x_1369_, 2, v___x_1366_);
    return v___x_1369_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__5_once),
        _init_l_Lake_DSL_requireDecl___closed__5,
    );
    v___x_1371_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1372_ = l_Lake_DSL_requireDecl___closed__1;
    v___x_1373_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1373_, 0, v___x_1372_);
    leanh::lean_ctor_set(v___x_1373_, 1, v___x_1371_);
    leanh::lean_ctor_set(v___x_1373_, 2, v___x_1370_);
    return v___x_1373_;
}
pub unsafe fn _init_l_Lake_DSL_requireDecl() -> *mut leanh::LeanObject {
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_requireDecl___closed__6_once),
        _init_l_Lake_DSL_requireDecl___closed__6,
    );
    return v___x_1374_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__9_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__9,
    );
    v___x_1382_ = l_Lake_DSL_identOrStr;
    v___x_1383_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1384_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1384_, 0, v___x_1383_);
    leanh::lean_ctor_set(v___x_1384_, 1, v___x_1382_);
    leanh::lean_ctor_set(v___x_1384_, 2, v___x_1381_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lake_DSL_buildDeclSig___closed__5;
    v___x_1394_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1395_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1396_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1396_, 0, v___x_1395_);
    leanh::lean_ctor_set(v___x_1396_, 1, v___x_1394_);
    leanh::lean_ctor_set(v___x_1396_, 2, v___x_1393_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__6_once),
        _init_l_Lake_DSL_buildDeclSig___closed__6,
    );
    v___x_1399_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1400_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1400_, 0, v___x_1399_);
    leanh::lean_ctor_set(v___x_1400_, 1, v___x_1398_);
    leanh::lean_ctor_set(v___x_1400_, 2, v___x_1397_);
    return v___x_1400_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__7_once),
        _init_l_Lake_DSL_buildDeclSig___closed__7,
    );
    v___x_1402_ = l_Lake_DSL_buildDeclSig___closed__1;
    v___x_1403_ = l_Lake_DSL_buildDeclSig___closed__0;
    v___x_1404_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    leanh::lean_ctor_set(v___x_1404_, 1, v___x_1402_);
    leanh::lean_ctor_set(v___x_1404_, 2, v___x_1401_);
    return v___x_1404_;
}
pub unsafe fn _init_l_Lake_DSL_buildDeclSig() -> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__8),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__8_once),
        _init_l_Lake_DSL_buildDeclSig___closed__8,
    );
    return v___x_1405_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1418_ = l_Lake_DSL_buildDeclSig;
    v___x_1419_ = l_Lake_DSL_moduleFacetDecl___closed__4;
    v___x_1420_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1421_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1421_, 0, v___x_1420_);
    leanh::lean_ctor_set(v___x_1421_, 1, v___x_1419_);
    leanh::lean_ctor_set(v___x_1421_, 2, v___x_1418_);
    return v___x_1421_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__5_once),
        _init_l_Lake_DSL_moduleFacetDecl___closed__5,
    );
    v___x_1423_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1424_ = l_Lake_DSL_moduleFacetDecl___closed__1;
    v___x_1425_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1425_, 0, v___x_1424_);
    leanh::lean_ctor_set(v___x_1425_, 1, v___x_1423_);
    leanh::lean_ctor_set(v___x_1425_, 2, v___x_1422_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lake_DSL_moduleFacetDecl() -> *mut leanh::LeanObject {
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_moduleFacetDecl___closed__6_once),
        _init_l_Lake_DSL_moduleFacetDecl___closed__6,
    );
    return v___x_1426_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lake_DSL_buildDeclSig;
    v___x_1440_ = l_Lake_DSL_packageFacetDecl___closed__4;
    v___x_1441_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1442_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    leanh::lean_ctor_set(v___x_1442_, 1, v___x_1440_);
    leanh::lean_ctor_set(v___x_1442_, 2, v___x_1439_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__5_once),
        _init_l_Lake_DSL_packageFacetDecl___closed__5,
    );
    v___x_1444_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1445_ = l_Lake_DSL_packageFacetDecl___closed__1;
    v___x_1446_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    leanh::lean_ctor_set(v___x_1446_, 1, v___x_1444_);
    leanh::lean_ctor_set(v___x_1446_, 2, v___x_1443_);
    return v___x_1446_;
}
pub unsafe fn _init_l_Lake_DSL_packageFacetDecl() -> *mut leanh::LeanObject {
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1447_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageFacetDecl___closed__6_once),
        _init_l_Lake_DSL_packageFacetDecl___closed__6,
    );
    return v___x_1447_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Lake_DSL_buildDeclSig;
    v___x_1461_ = l_Lake_DSL_libraryFacetDecl___closed__4;
    v___x_1462_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1463_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1463_, 0, v___x_1462_);
    leanh::lean_ctor_set(v___x_1463_, 1, v___x_1461_);
    leanh::lean_ctor_set(v___x_1463_, 2, v___x_1460_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__5_once),
        _init_l_Lake_DSL_libraryFacetDecl___closed__5,
    );
    v___x_1465_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1466_ = l_Lake_DSL_libraryFacetDecl___closed__1;
    v___x_1467_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    leanh::lean_ctor_set(v___x_1467_, 1, v___x_1465_);
    leanh::lean_ctor_set(v___x_1467_, 2, v___x_1464_);
    return v___x_1467_;
}
pub unsafe fn _init_l_Lake_DSL_libraryFacetDecl() -> *mut leanh::LeanObject {
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_libraryFacetDecl___closed__6_once),
        _init_l_Lake_DSL_libraryFacetDecl___closed__6,
    );
    return v___x_1468_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lake_DSL_buildDeclSig;
    v___x_1482_ = l_Lake_DSL_targetCommand___closed__4;
    v___x_1483_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1484_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1484_, 0, v___x_1483_);
    leanh::lean_ctor_set(v___x_1484_, 1, v___x_1482_);
    leanh::lean_ctor_set(v___x_1484_, 2, v___x_1481_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__5_once),
        _init_l_Lake_DSL_targetCommand___closed__5,
    );
    v___x_1486_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1487_ = l_Lake_DSL_targetCommand___closed__1;
    v___x_1488_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
    leanh::lean_ctor_set(v___x_1488_, 1, v___x_1486_);
    leanh::lean_ctor_set(v___x_1488_, 2, v___x_1485_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lake_DSL_targetCommand() -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_targetCommand___closed__6_once),
        _init_l_Lake_DSL_targetCommand___closed__6,
    );
    return v___x_1489_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1503_ = l_Lake_DSL_leanLibCommand___closed__4;
    v___x_1504_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1505_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
    leanh::lean_ctor_set(v___x_1505_, 1, v___x_1503_);
    leanh::lean_ctor_set(v___x_1505_, 2, v___x_1502_);
    return v___x_1505_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = l_Lake_DSL_optConfig;
    v___x_1507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__5_once),
        _init_l_Lake_DSL_leanLibCommand___closed__5,
    );
    v___x_1508_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1509_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1509_, 0, v___x_1508_);
    leanh::lean_ctor_set(v___x_1509_, 1, v___x_1507_);
    leanh::lean_ctor_set(v___x_1509_, 2, v___x_1506_);
    return v___x_1509_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__6_once),
        _init_l_Lake_DSL_leanLibCommand___closed__6,
    );
    v___x_1511_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1512_ = l_Lake_DSL_leanLibCommand___closed__1;
    v___x_1513_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    leanh::lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    leanh::lean_ctor_set(v___x_1513_, 2, v___x_1510_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lake_DSL_leanLibCommand() -> *mut leanh::LeanObject {
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanLibCommand___closed__7_once),
        _init_l_Lake_DSL_leanLibCommand___closed__7,
    );
    return v___x_1514_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1529_ = l_Lake_DSL_leanExeCommand___closed__4;
    v___x_1530_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1531_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    leanh::lean_ctor_set(v___x_1531_, 1, v___x_1529_);
    leanh::lean_ctor_set(v___x_1531_, 2, v___x_1528_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ = l_Lake_DSL_optConfig;
    v___x_1533_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__5_once),
        _init_l_Lake_DSL_leanExeCommand___closed__5,
    );
    v___x_1534_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1535_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    leanh::lean_ctor_set(v___x_1535_, 1, v___x_1533_);
    leanh::lean_ctor_set(v___x_1535_, 2, v___x_1532_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__6_once),
        _init_l_Lake_DSL_leanExeCommand___closed__6,
    );
    v___x_1537_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1538_ = l_Lake_DSL_leanExeCommand___closed__1;
    v___x_1539_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1539_, 0, v___x_1538_);
    leanh::lean_ctor_set(v___x_1539_, 1, v___x_1537_);
    leanh::lean_ctor_set(v___x_1539_, 2, v___x_1536_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lake_DSL_leanExeCommand() -> *mut leanh::LeanObject {
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_leanExeCommand___closed__7_once),
        _init_l_Lake_DSL_leanExeCommand___closed__7,
    );
    return v___x_1540_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1555_ = l_Lake_DSL_inputFileCommand___closed__4;
    v___x_1556_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1557_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    leanh::lean_ctor_set(v___x_1557_, 1, v___x_1555_);
    leanh::lean_ctor_set(v___x_1557_, 2, v___x_1554_);
    return v___x_1557_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = l_Lake_DSL_optConfig;
    v___x_1559_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__5_once),
        _init_l_Lake_DSL_inputFileCommand___closed__5,
    );
    v___x_1560_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1561_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    leanh::lean_ctor_set(v___x_1561_, 1, v___x_1559_);
    leanh::lean_ctor_set(v___x_1561_, 2, v___x_1558_);
    return v___x_1561_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__6_once),
        _init_l_Lake_DSL_inputFileCommand___closed__6,
    );
    v___x_1563_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1564_ = l_Lake_DSL_inputFileCommand___closed__1;
    v___x_1565_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    leanh::lean_ctor_set(v___x_1565_, 1, v___x_1563_);
    leanh::lean_ctor_set(v___x_1565_, 2, v___x_1562_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Lake_DSL_inputFileCommand() -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputFileCommand___closed__7_once),
        _init_l_Lake_DSL_inputFileCommand___closed__7,
    );
    return v___x_1566_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19),
        core::ptr::addr_of_mut!(l_Lake_DSL_packageCommand___closed__19_once),
        _init_l_Lake_DSL_packageCommand___closed__19,
    );
    v___x_1581_ = l_Lake_DSL_inputDirCommand___closed__4;
    v___x_1582_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1583_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1583_, 0, v___x_1582_);
    leanh::lean_ctor_set(v___x_1583_, 1, v___x_1581_);
    leanh::lean_ctor_set(v___x_1583_, 2, v___x_1580_);
    return v___x_1583_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lake_DSL_optConfig;
    v___x_1585_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__5_once),
        _init_l_Lake_DSL_inputDirCommand___closed__5,
    );
    v___x_1586_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1587_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1587_, 0, v___x_1586_);
    leanh::lean_ctor_set(v___x_1587_, 1, v___x_1585_);
    leanh::lean_ctor_set(v___x_1587_, 2, v___x_1584_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__6_once),
        _init_l_Lake_DSL_inputDirCommand___closed__6,
    );
    v___x_1589_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1590_ = l_Lake_DSL_inputDirCommand___closed__1;
    v___x_1591_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1591_, 0, v___x_1590_);
    leanh::lean_ctor_set(v___x_1591_, 1, v___x_1589_);
    leanh::lean_ctor_set(v___x_1591_, 2, v___x_1588_);
    return v___x_1591_;
}
pub unsafe fn _init_l_Lake_DSL_inputDirCommand() -> *mut leanh::LeanObject {
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__7),
        core::ptr::addr_of_mut!(l_Lake_DSL_inputDirCommand___closed__7_once),
        _init_l_Lake_DSL_inputDirCommand___closed__7,
    );
    return v___x_1592_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lake_DSL_postUpdateDecl___closed__16;
    v___x_1600_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1601_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1602_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1602_, 0, v___x_1601_);
    leanh::lean_ctor_set(v___x_1602_, 1, v___x_1600_);
    leanh::lean_ctor_set(v___x_1602_, 2, v___x_1599_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__2_once),
        _init_l_Lake_DSL_externLibDeclSpec___closed__2,
    );
    v___x_1604_ = l_Lake_DSL_externLibDeclSpec___closed__1;
    v___x_1605_ = l_Lake_DSL_externLibDeclSpec___closed__0;
    v___x_1606_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
    leanh::lean_ctor_set(v___x_1606_, 1, v___x_1604_);
    leanh::lean_ctor_set(v___x_1606_, 2, v___x_1603_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Lake_DSL_externLibDeclSpec() -> *mut leanh::LeanObject {
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibDeclSpec___closed__3_once),
        _init_l_Lake_DSL_externLibDeclSpec___closed__3,
    );
    return v___x_1607_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lake_DSL_externLibDeclSpec;
    v___x_1621_ = l_Lake_DSL_externLibCommand___closed__4;
    v___x_1622_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1623_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1623_, 0, v___x_1622_);
    leanh::lean_ctor_set(v___x_1623_, 1, v___x_1621_);
    leanh::lean_ctor_set(v___x_1623_, 2, v___x_1620_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__5_once),
        _init_l_Lake_DSL_externLibCommand___closed__5,
    );
    v___x_1625_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1626_ = l_Lake_DSL_externLibCommand___closed__1;
    v___x_1627_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1627_, 0, v___x_1626_);
    leanh::lean_ctor_set(v___x_1627_, 1, v___x_1625_);
    leanh::lean_ctor_set(v___x_1627_, 2, v___x_1624_);
    return v___x_1627_;
}
pub unsafe fn _init_l_Lake_DSL_externLibCommand() -> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_externLibCommand___closed__6_once),
        _init_l_Lake_DSL_externLibCommand___closed__6,
    );
    return v___x_1628_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17),
        core::ptr::addr_of_mut!(l_Lake_DSL_postUpdateDecl___closed__17_once),
        _init_l_Lake_DSL_postUpdateDecl___closed__17,
    );
    v___x_1635_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_buildDeclSig___closed__2_once),
        _init_l_Lake_DSL_buildDeclSig___closed__2,
    );
    v___x_1636_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1637_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1637_, 0, v___x_1636_);
    leanh::lean_ctor_set(v___x_1637_, 1, v___x_1635_);
    leanh::lean_ctor_set(v___x_1637_, 2, v___x_1634_);
    return v___x_1637_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__2_once),
        _init_l_Lake_DSL_scriptDeclSpec___closed__2,
    );
    v___x_1639_ = l_Lake_DSL_scriptDeclSpec___closed__1;
    v___x_1640_ = l_Lake_DSL_scriptDeclSpec___closed__0;
    v___x_1641_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1641_, 0, v___x_1640_);
    leanh::lean_ctor_set(v___x_1641_, 1, v___x_1639_);
    leanh::lean_ctor_set(v___x_1641_, 2, v___x_1638_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDeclSpec() -> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDeclSpec___closed__3_once),
        _init_l_Lake_DSL_scriptDeclSpec___closed__3,
    );
    return v___x_1642_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lake_DSL_scriptDeclSpec;
    v___x_1656_ = l_Lake_DSL_scriptDecl___closed__4;
    v___x_1657_ = l_Lake_DSL_getConfig___closed__3;
    v___x_1658_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1658_, 0, v___x_1657_);
    leanh::lean_ctor_set(v___x_1658_, 1, v___x_1656_);
    leanh::lean_ctor_set(v___x_1658_, 2, v___x_1655_);
    return v___x_1658_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__5),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__5_once),
        _init_l_Lake_DSL_scriptDecl___closed__5,
    );
    v___x_1660_ = leanh::lean_unsigned_to_nat(1022);
    v___x_1661_ = l_Lake_DSL_scriptDecl___closed__1;
    v___x_1662_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    leanh::lean_ctor_set(v___x_1662_, 1, v___x_1660_);
    leanh::lean_ctor_set(v___x_1662_, 2, v___x_1659_);
    return v___x_1662_;
}
pub unsafe fn _init_l_Lake_DSL_scriptDecl() -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__6),
        core::ptr::addr_of_mut!(l_Lake_DSL_scriptDecl___closed__6_once),
        _init_l_Lake_DSL_scriptDecl___closed__6,
    );
    return v___x_1663_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_DeclUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_DSL_packageCommand = _init_l_Lake_DSL_packageCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_packageCommand);
    l_Lake_DSL_postUpdateDecl = _init_l_Lake_DSL_postUpdateDecl();
    leanh::lean_mark_persistent(l_Lake_DSL_postUpdateDecl);
    l_Lake_DSL_depName = _init_l_Lake_DSL_depName();
    leanh::lean_mark_persistent(l_Lake_DSL_depName);
    l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
    leanh::lean_mark_persistent(l_Lake_DSL_depSpec);
    l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
    leanh::lean_mark_persistent(l_Lake_DSL_requireDecl);
    l_Lake_DSL_buildDeclSig = _init_l_Lake_DSL_buildDeclSig();
    leanh::lean_mark_persistent(l_Lake_DSL_buildDeclSig);
    l_Lake_DSL_moduleFacetDecl = _init_l_Lake_DSL_moduleFacetDecl();
    leanh::lean_mark_persistent(l_Lake_DSL_moduleFacetDecl);
    l_Lake_DSL_packageFacetDecl = _init_l_Lake_DSL_packageFacetDecl();
    leanh::lean_mark_persistent(l_Lake_DSL_packageFacetDecl);
    l_Lake_DSL_libraryFacetDecl = _init_l_Lake_DSL_libraryFacetDecl();
    leanh::lean_mark_persistent(l_Lake_DSL_libraryFacetDecl);
    l_Lake_DSL_targetCommand = _init_l_Lake_DSL_targetCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_targetCommand);
    l_Lake_DSL_leanLibCommand = _init_l_Lake_DSL_leanLibCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_leanLibCommand);
    l_Lake_DSL_leanExeCommand = _init_l_Lake_DSL_leanExeCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_leanExeCommand);
    l_Lake_DSL_inputFileCommand = _init_l_Lake_DSL_inputFileCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_inputFileCommand);
    l_Lake_DSL_inputDirCommand = _init_l_Lake_DSL_inputDirCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_inputDirCommand);
    l_Lake_DSL_externLibDeclSpec = _init_l_Lake_DSL_externLibDeclSpec();
    leanh::lean_mark_persistent(l_Lake_DSL_externLibDeclSpec);
    l_Lake_DSL_externLibCommand = _init_l_Lake_DSL_externLibCommand();
    leanh::lean_mark_persistent(l_Lake_DSL_externLibCommand);
    l_Lake_DSL_scriptDeclSpec = _init_l_Lake_DSL_scriptDeclSpec();
    leanh::lean_mark_persistent(l_Lake_DSL_scriptDeclSpec);
    l_Lake_DSL_scriptDecl = _init_l_Lake_DSL_scriptDecl();
    leanh::lean_mark_persistent(l_Lake_DSL_scriptDecl);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_DeclUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Syntax(builtin);
}