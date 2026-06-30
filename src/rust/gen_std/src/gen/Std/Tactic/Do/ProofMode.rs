// Lean compiler output
// Module: Std.Tactic.Do.ProofMode
// Imports: Std.Do.SPred.SPred
use crate::r#gen::Std::Do::SPred::SPred::{
    initialize_Std_Do_SPred_SPred, runtime_initialize_Std_Do_SPred_SPred,
};
pub static l_Std_Tactic_Do_mgoalHyp___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [109, 103, 111, 97, 108, 72, 121, 112, 0],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__1_value: leanh::LeanStringObject<4> =
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
static mut l_Std_Tactic_Do_mgoalHyp___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__3_value: leanh::LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__1_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__2_value)
                as *mut leanh::LeanObject,
            5139300886809190733 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__3_value)
                as *mut leanh::LeanObject,
            1041404937882640577 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Tactic_Do_mgoalHyp___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__0_value)
                as *mut leanh::LeanObject,
            1824513113201743363 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__5_value: leanh::LeanStringObject<8> =
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
static mut l_Std_Tactic_Do_mgoalHyp___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__5_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__7_value: leanh::LeanStringObject<6> =
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
static mut l_Std_Tactic_Do_mgoalHyp___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__7_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__10_value: leanh::LeanStringObject<4> =
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
        m_data: [32, 58, 32, 0],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__11_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__13_value: leanh::LeanStringObject<5> =
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
static mut l_Std_Tactic_Do_mgoalHyp___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__13_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__15_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__14_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalHyp___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalHyp___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__17_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_Do_mgoalHyp: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [109, 103, 111, 97, 108, 83, 116, 120, 0],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__1_value)
                as *mut leanh::LeanObject,
            15734321041234825264 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__2_value)
                as *mut leanh::LeanObject,
            5139300886809190733 as *mut leanh::LeanObject,
        ],
    };
static l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__3_value)
                as *mut leanh::LeanObject,
            1041404937882640577 as *mut leanh::LeanObject,
        ],
    };
pub static l_Std_Tactic_Do_mgoalStx___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__0_value)
                as *mut leanh::LeanObject,
            2380567982751280064 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__2_value: leanh::LeanStringObject<5> =
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
static mut l_Std_Tactic_Do_mgoalStx___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__2_value)
                as *mut leanh::LeanObject,
            2302572775315350313 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__4_value: leanh::LeanStringObject<9> =
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
        m_data: [112, 112, 68, 101, 100, 101, 110, 116, 0],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__4_value)
                as *mut leanh::LeanObject,
            2710995909225096690 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__6_value: leanh::LeanStringObject<7> =
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
        m_data: [112, 112, 76, 105, 110, 101, 0],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__6_value)
                as *mut leanh::LeanObject,
            4227538229121138037 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__8_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__11_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__12_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 3,
        m_data: [226, 138, 162, 226, 130, 155, 32, 0],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__13_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__16_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalHyp___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_Do_mgoalStx___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Tactic_Do_mgoalStx___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__18_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_Do_mgoalStx: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_Do_mgoalStx___closed__18_value)
        as *mut leanh::LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_Do_ProofMode(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_Do_ProofMode(
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
pub unsafe fn initialize_Std_Tactic_Do_ProofMode(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred_SPred(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_ProofMode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_Do_ProofMode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_Do_ProofMode(builtin);
}