// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
// Imports: Lean.Meta.Tactic.Simp.Simproc
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constLevels_x21, l_Lean_mkApp3,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkDecide, l_Lean_Meta_mkEqRefl};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value:
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
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        15761733860085307253 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value:
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
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        907667957179513571 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value:
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
        101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 100, 101, 99, 105, 100, 101, 0,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        4053297232167869867 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        9255189395584251158 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value:
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
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value)
            as *mut leanh::LeanObject,
        11870096045526947150 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
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
        101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 100, 101, 99, 105, 100, 101, 0,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value)
            as *mut leanh::LeanObject,
        10755389243347010570 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__0_value: leanh::LeanStringObject<9> =
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
        m_data: [101, 113, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__0_value)
                as *mut leanh::LeanObject,
            1953906391527423986 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__3_value: leanh::LeanStringObject<8> =
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
        m_data: [101, 113, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__3_value)
                as *mut leanh::LeanObject,
            12633671826946381106 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__6_value: leanh::LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__7_value: leanh::LeanStringObject<5> =
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
        m_data: [114, 101, 102, 108, 0],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_evalEqPropStep___closed__8_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__6_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__8_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__7_value)
                as *mut leanh::LeanObject,
            13480818501600609864 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalNePropStep___closed__0_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__6_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalNePropStep___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalNePropStep___closed__1_value: leanh::LeanStringObject<14> =
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
            110, 111, 116, 95, 110, 111, 116, 95, 105, 110, 116, 114, 111, 0,
        ],
    };
static mut l_Lean_Meta_Simp_evalNePropStep___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_evalNePropStep___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__1_value)
                as *mut leanh::LeanObject,
            5766767816827580045 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalNePropStep___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_evalNePropStep___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_evalNePropStep___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = leanh::lean_box(0);
    v___x_322_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__2;
    v___x_323_ = l_Lean_mkConst(v___x_322_, v___x_321_);
    return v___x_323_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = leanh::lean_box(0);
    v___x_328_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__5;
    v___x_329_ = l_Lean_mkConst(v___x_328_, v___x_327_);
    return v___x_329_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = leanh::lean_box(0);
    v___x_334_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__8;
    v___x_335_ = l_Lean_mkConst(v___x_334_, v___x_333_);
    return v___x_335_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = leanh::lean_box(0);
    v___x_341_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__11;
    v___x_342_ = l_Lean_mkConst(v___x_341_, v___x_340_);
    return v___x_342_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = leanh::lean_box(0);
    v___x_347_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__14;
    v___x_348_ = l_Lean_mkConst(v___x_347_, v___x_346_);
    return v___x_348_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_352_ = leanh::lean_box(0);
    v___x_353_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__17;
    v___x_354_ = l_Lean_mkConst(v___x_353_, v___x_352_);
    return v___x_354_;
}
pub unsafe fn l_Lean_Meta_Simp_evalPropStep___redArg(
    mut v_p_355_: *mut leanh::LeanObject,
    mut v_result_356_: u8,
    mut v_a_357_: *mut leanh::LeanObject,
    mut v_a_358_: *mut leanh::LeanObject,
    mut v_a_359_: *mut leanh::LeanObject,
    mut v_a_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: u8 = 0;
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v_a_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_390_: u8 = 0;
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_394_: u8 = 0;
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_400_: u8 = 0;
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut v_a_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_420_: u8 = 0;
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut v_a_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_428_: u8 = 0;
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_355_);
                v___x_362_ = l_Lean_Meta_mkDecide(v_p_355_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
                if leanh::lean_obj_tag(v___x_362_) == 0 {
                    v_a_363_ = leanh::lean_ctor_get(v___x_362_, 0);
                    leanh::lean_inc(v_a_363_);
                    leanh::lean_dec_ref_known(v___x_362_, 1);
                    v___x_364_ = 1;
                    if v_result_356_ == 0 {
                        v___x_365_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_evalPropStep___redArg___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once
                            ),
                            _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3,
                        );
                        v___x_366_ = l_Lean_Meta_mkEqRefl(
                            v___x_365_, v_a_357_, v_a_358_, v_a_359_, v_a_360_,
                        );
                        if leanh::lean_obj_tag(v___x_366_) == 0 {
                            v_a_367_ = leanh::lean_ctor_get(v___x_366_, 0);
                            v_isSharedCheck_386_ =
                                (!leanh::lean_is_exclusive(v___x_366_)) as u8;
                            if v_isSharedCheck_386_ == 0 {
                                v___x_369_ = v___x_366_;
                                v_isShared_370_ = v_isSharedCheck_386_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_367_);
                                leanh::lean_dec(v___x_366_);
                                v___x_369_ = leanh::lean_box(0);
                                v_isShared_370_ = v_isSharedCheck_386_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_363_);
                            leanh::lean_dec_ref(v_p_355_);
                            v_a_387_ = leanh::lean_ctor_get(v___x_366_, 0);
                            v_isSharedCheck_394_ =
                                (!leanh::lean_is_exclusive(v___x_366_)) as u8;
                            if v_isSharedCheck_394_ == 0 {
                                v___x_389_ = v___x_366_;
                                v_isShared_390_ = v_isSharedCheck_394_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_387_);
                                leanh::lean_dec(v___x_366_);
                                v___x_389_ = leanh::lean_box(0);
                                v_isShared_390_ = v_isSharedCheck_394_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_395_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_evalPropStep___redArg___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once
                            ),
                            _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12,
                        );
                        v___x_396_ = l_Lean_Meta_mkEqRefl(
                            v___x_395_, v_a_357_, v_a_358_, v_a_359_, v_a_360_,
                        );
                        if leanh::lean_obj_tag(v___x_396_) == 0 {
                            v_a_397_ = leanh::lean_ctor_get(v___x_396_, 0);
                            v_isSharedCheck_416_ =
                                (!leanh::lean_is_exclusive(v___x_396_)) as u8;
                            if v_isSharedCheck_416_ == 0 {
                                v___x_399_ = v___x_396_;
                                v_isShared_400_ = v_isSharedCheck_416_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_397_);
                                leanh::lean_dec(v___x_396_);
                                v___x_399_ = leanh::lean_box(0);
                                v_isShared_400_ = v_isSharedCheck_416_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_363_);
                            leanh::lean_dec_ref(v_p_355_);
                            v_a_417_ = leanh::lean_ctor_get(v___x_396_, 0);
                            v_isSharedCheck_424_ =
                                (!leanh::lean_is_exclusive(v___x_396_)) as u8;
                            if v_isSharedCheck_424_ == 0 {
                                v___x_419_ = v___x_396_;
                                v_isShared_420_ = v_isSharedCheck_424_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_417_);
                                leanh::lean_dec(v___x_396_);
                                v___x_419_ = leanh::lean_box(0);
                                v_isShared_420_ = v_isSharedCheck_424_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_p_355_);
                    v_a_425_ = leanh::lean_ctor_get(v___x_362_, 0);
                    v_isSharedCheck_432_ = (!leanh::lean_is_exclusive(v___x_362_)) as u8;
                    if v_isSharedCheck_432_ == 0 {
                        v___x_427_ = v___x_362_;
                        v_isShared_428_ = v_isSharedCheck_432_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_425_);
                        leanh::lean_dec(v___x_362_);
                        v___x_427_ = leanh::lean_box(0);
                        v_isShared_428_ = v_isSharedCheck_432_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_371_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6,
                );
                v___x_372_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9,
                );
                v___x_373_ = l_Lean_Expr_appArg_x21(v_a_363_);
                leanh::lean_dec(v_a_363_);
                v___x_374_ = leanh::lean_unsigned_to_nat(3);
                v___x_375_ = lean_mk_empty_array_with_capacity(v___x_374_);
                v___x_376_ = lean_array_push(v___x_375_, v_p_355_);
                v___x_377_ = lean_array_push(v___x_376_, v___x_373_);
                v___x_378_ = lean_array_push(v___x_377_, v_a_367_);
                v___x_379_ = l_Lean_mkAppN(v___x_372_, v___x_378_);
                leanh::lean_dec_ref(v___x_378_);
                v___x_380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_380_, 0, v___x_379_);
                v___x_381_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_381_, 0, v___x_371_);
                leanh::lean_ctor_set(v___x_381_, 1, v___x_380_);
                leanh::lean_ctor_set_uint8(
                    v___x_381_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_364_,
                );
                v___x_382_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_382_, 0, v___x_381_);
                if v_isShared_370_ == 0 {
                    leanh::lean_ctor_set(v___x_369_, 0, v___x_382_);
                    v___x_384_ = v___x_369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
                    v___x_384_ = v_reuseFailAlloc_385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_384_;
            }
            3 => {
                if v_isShared_390_ == 0 {
                    v___x_392_ = v___x_389_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
                    v___x_392_ = v_reuseFailAlloc_393_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_392_;
            }
            5 => {
                v___x_401_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15,
                );
                v___x_402_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__18),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18,
                );
                v___x_403_ = l_Lean_Expr_appArg_x21(v_a_363_);
                leanh::lean_dec(v_a_363_);
                v___x_404_ = leanh::lean_unsigned_to_nat(3);
                v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
                v___x_406_ = lean_array_push(v___x_405_, v_p_355_);
                v___x_407_ = lean_array_push(v___x_406_, v___x_403_);
                v___x_408_ = lean_array_push(v___x_407_, v_a_397_);
                v___x_409_ = l_Lean_mkAppN(v___x_402_, v___x_408_);
                leanh::lean_dec_ref(v___x_408_);
                v___x_410_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_410_, 0, v___x_409_);
                v___x_411_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_411_, 0, v___x_401_);
                leanh::lean_ctor_set(v___x_411_, 1, v___x_410_);
                leanh::lean_ctor_set_uint8(
                    v___x_411_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_364_,
                );
                v___x_412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_412_, 0, v___x_411_);
                if v_isShared_400_ == 0 {
                    leanh::lean_ctor_set(v___x_399_, 0, v___x_412_);
                    v___x_414_ = v___x_399_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_415_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
                    v___x_414_ = v_reuseFailAlloc_415_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_414_;
            }
            7 => {
                if v_isShared_420_ == 0 {
                    v___x_422_ = v___x_419_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_423_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
                    v___x_422_ = v_reuseFailAlloc_423_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_422_;
            }
            9 => {
                if v_isShared_428_ == 0 {
                    v___x_430_ = v___x_427_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
                    v___x_430_ = v_reuseFailAlloc_431_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_evalPropStep___redArg___boxed(
    mut v_p_433_: *mut leanh::LeanObject,
    mut v_result_434_: *mut leanh::LeanObject,
    mut v_a_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_a_437_: *mut leanh::LeanObject,
    mut v_a_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_boxed_440_: u8 = 0;
    let mut v_res_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_boxed_440_ = (leanh::lean_unbox(v_result_434_) as u8);
    v_res_441_ = l_Lean_Meta_Simp_evalPropStep___redArg(
        v_p_433_,
        v_result_boxed_440_,
        v_a_435_,
        v_a_436_,
        v_a_437_,
        v_a_438_,
    );
    leanh::lean_dec(v_a_438_);
    leanh::lean_dec_ref(v_a_437_);
    leanh::lean_dec(v_a_436_);
    leanh::lean_dec_ref(v_a_435_);
    return v_res_441_;
}
pub unsafe fn l_Lean_Meta_Simp_evalPropStep(
    mut v_p_442_: *mut leanh::LeanObject,
    mut v_result_443_: u8,
    mut v_a_444_: *mut leanh::LeanObject,
    mut v_a_445_: *mut leanh::LeanObject,
    mut v_a_446_: *mut leanh::LeanObject,
    mut v_a_447_: *mut leanh::LeanObject,
    mut v_a_448_: *mut leanh::LeanObject,
    mut v_a_449_: *mut leanh::LeanObject,
    mut v_a_450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_Meta_Simp_evalPropStep___redArg(
        v_p_442_,
        v_result_443_,
        v_a_447_,
        v_a_448_,
        v_a_449_,
        v_a_450_,
    );
    return v___x_452_;
}
pub unsafe fn l_Lean_Meta_Simp_evalPropStep___boxed(
    mut v_p_453_: *mut leanh::LeanObject,
    mut v_result_454_: *mut leanh::LeanObject,
    mut v_a_455_: *mut leanh::LeanObject,
    mut v_a_456_: *mut leanh::LeanObject,
    mut v_a_457_: *mut leanh::LeanObject,
    mut v_a_458_: *mut leanh::LeanObject,
    mut v_a_459_: *mut leanh::LeanObject,
    mut v_a_460_: *mut leanh::LeanObject,
    mut v_a_461_: *mut leanh::LeanObject,
    mut v_a_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_boxed_463_: u8 = 0;
    let mut v_res_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_boxed_463_ = (leanh::lean_unbox(v_result_454_) as u8);
    v_res_464_ = l_Lean_Meta_Simp_evalPropStep(
        v_p_453_,
        v_result_boxed_463_,
        v_a_455_,
        v_a_456_,
        v_a_457_,
        v_a_458_,
        v_a_459_,
        v_a_460_,
        v_a_461_,
    );
    leanh::lean_dec(v_a_461_);
    leanh::lean_dec_ref(v_a_460_);
    leanh::lean_dec(v_a_459_);
    leanh::lean_dec_ref(v_a_458_);
    leanh::lean_dec(v_a_457_);
    leanh::lean_dec_ref(v_a_456_);
    leanh::lean_dec(v_a_455_);
    return v_res_464_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ = leanh::lean_box(0);
    v___x_469_ = l_Lean_Meta_Simp_evalEqPropStep___closed__1;
    v___x_470_ = l_Lean_mkConst(v___x_469_, v___x_468_);
    return v___x_470_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = leanh::lean_box(0);
    v___x_475_ = l_Lean_Meta_Simp_evalEqPropStep___closed__4;
    v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_474_);
    return v___x_476_;
}
pub unsafe fn l_Lean_Meta_Simp_evalEqPropStep(
    mut v_e_482_: *mut leanh::LeanObject,
    mut v_eq_483_: u8,
    mut v_mkNeProof_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_a_489_: *mut leanh::LeanObject,
    mut v_a_490_: *mut leanh::LeanObject,
    mut v_a_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_493_: u8 = 0;
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut v_a_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_493_ = 1;
                if v_eq_483_ == 0 {
                    leanh::lean_inc(v_a_491_);
                    leanh::lean_inc_ref(v_a_490_);
                    leanh::lean_inc(v_a_489_);
                    leanh::lean_inc_ref(v_a_488_);
                    leanh::lean_inc(v_a_487_);
                    leanh::lean_inc_ref(v_a_486_);
                    leanh::lean_inc(v_a_485_);
                    v___x_494_ = leanh::lean_apply_8(
                        v_mkNeProof_484_,
                        v_a_485_,
                        v_a_486_,
                        v_a_487_,
                        v_a_488_,
                        v_a_489_,
                        v_a_490_,
                        v_a_491_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_494_) == 0 {
                        v_a_495_ = leanh::lean_ctor_get(v___x_494_, 0);
                        v_isSharedCheck_508_ = (!leanh::lean_is_exclusive(v___x_494_)) as u8;
                        if v_isSharedCheck_508_ == 0 {
                            v___x_497_ = v___x_494_;
                            v_isShared_498_ = v_isSharedCheck_508_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_495_);
                            leanh::lean_dec(v___x_494_);
                            v___x_497_ = leanh::lean_box(0);
                            v_isShared_498_ = v_isSharedCheck_508_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_482_);
                        v_a_509_ = leanh::lean_ctor_get(v___x_494_, 0);
                        v_isSharedCheck_516_ = (!leanh::lean_is_exclusive(v___x_494_)) as u8;
                        if v_isSharedCheck_516_ == 0 {
                            v___x_511_ = v___x_494_;
                            v_isShared_512_ = v_isSharedCheck_516_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_509_);
                            leanh::lean_dec(v___x_494_);
                            v___x_511_ = leanh::lean_box(0);
                            v_isShared_512_ = v_isSharedCheck_516_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_mkNeProof_484_);
                    v___x_517_ = leanh::lean_box(0);
                    v___x_518_ = l_Lean_Expr_appFn_x21(v_e_482_);
                    v___x_519_ = l_Lean_Expr_appFn_x21(v___x_518_);
                    v_00_u03b1_520_ = l_Lean_Expr_appArg_x21(v___x_519_);
                    v_a_521_ = l_Lean_Expr_appArg_x21(v___x_518_);
                    leanh::lean_dec_ref(v___x_518_);
                    v___x_522_ = l_Lean_Expr_appFn_x21(v___x_519_);
                    leanh::lean_dec_ref(v___x_519_);
                    v___x_523_ = l_Lean_Expr_constLevels_x21(v___x_522_);
                    leanh::lean_dec_ref(v___x_522_);
                    v_u_524_ = l_List_head_x21___redArg(v___x_517_, v___x_523_);
                    leanh::lean_dec(v___x_523_);
                    v___x_525_ = leanh::lean_box(0);
                    v___x_526_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5_once),
                        _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5,
                    );
                    v___x_527_ = l_Lean_Meta_Simp_evalEqPropStep___closed__8;
                    v___x_528_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_528_, 0, v_u_524_);
                    leanh::lean_ctor_set(v___x_528_, 1, v___x_525_);
                    v___x_529_ = l_Lean_mkConst(v___x_527_, v___x_528_);
                    v___x_530_ = l_Lean_mkAppB(v___x_529_, v_00_u03b1_520_, v_a_521_);
                    v_proof_531_ = l_Lean_mkAppB(v___x_526_, v_e_482_, v___x_530_);
                    v___x_532_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_evalPropStep___redArg___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once
                        ),
                        _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15,
                    );
                    v___x_533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_533_, 0, v_proof_531_);
                    v___x_534_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_534_, 0, v___x_532_);
                    leanh::lean_ctor_set(v___x_534_, 1, v___x_533_);
                    leanh::lean_ctor_set_uint8(
                        v___x_534_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_493_,
                    );
                    v___x_535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_535_, 0, v___x_534_);
                    v___x_536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
                    return v___x_536_;
                }
            }
            1 => {
                v___x_499_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2_once),
                    _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2,
                );
                v___x_500_ = l_Lean_mkAppB(v___x_499_, v_e_482_, v_a_495_);
                v___x_501_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6,
                );
                v___x_502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_502_, 0, v___x_500_);
                v___x_503_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_503_, 0, v___x_501_);
                leanh::lean_ctor_set(v___x_503_, 1, v___x_502_);
                leanh::lean_ctor_set_uint8(
                    v___x_503_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_493_,
                );
                v___x_504_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_504_, 0, v___x_503_);
                if v_isShared_498_ == 0 {
                    leanh::lean_ctor_set(v___x_497_, 0, v___x_504_);
                    v___x_506_ = v___x_497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_507_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
                    v___x_506_ = v_reuseFailAlloc_507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_506_;
            }
            3 => {
                if v_isShared_512_ == 0 {
                    v___x_514_ = v___x_511_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
                    v___x_514_ = v_reuseFailAlloc_515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_evalEqPropStep___boxed(
    mut v_e_537_: *mut leanh::LeanObject,
    mut v_eq_538_: *mut leanh::LeanObject,
    mut v_mkNeProof_539_: *mut leanh::LeanObject,
    mut v_a_540_: *mut leanh::LeanObject,
    mut v_a_541_: *mut leanh::LeanObject,
    mut v_a_542_: *mut leanh::LeanObject,
    mut v_a_543_: *mut leanh::LeanObject,
    mut v_a_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
    mut v_a_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eq_boxed_548_: u8 = 0;
    let mut v_res_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eq_boxed_548_ = (leanh::lean_unbox(v_eq_538_) as u8);
    v_res_549_ = l_Lean_Meta_Simp_evalEqPropStep(
        v_e_537_,
        v_eq_boxed_548_,
        v_mkNeProof_539_,
        v_a_540_,
        v_a_541_,
        v_a_542_,
        v_a_543_,
        v_a_544_,
        v_a_545_,
        v_a_546_,
    );
    leanh::lean_dec(v_a_546_);
    leanh::lean_dec_ref(v_a_545_);
    leanh::lean_dec(v_a_544_);
    leanh::lean_dec_ref(v_a_543_);
    leanh::lean_dec(v_a_542_);
    leanh::lean_dec_ref(v_a_541_);
    leanh::lean_dec(v_a_540_);
    return v_res_549_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalNePropStep___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_box(0);
    v___x_556_ = l_Lean_Meta_Simp_evalNePropStep___closed__2;
    v___x_557_ = l_Lean_mkConst(v___x_556_, v___x_555_);
    return v___x_557_;
}
pub unsafe fn l_Lean_Meta_Simp_evalNePropStep(
    mut v_e_558_: *mut leanh::LeanObject,
    mut v_ne_559_: u8,
    mut v_mkNeProof_560_: *mut leanh::LeanObject,
    mut v_a_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
    mut v_a_563_: *mut leanh::LeanObject,
    mut v_a_564_: *mut leanh::LeanObject,
    mut v_a_565_: *mut leanh::LeanObject,
    mut v_a_566_: *mut leanh::LeanObject,
    mut v_a_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqProp_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rflExpr_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_609_: u8 = 0;
    let mut v_a_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_569_ = 1;
                if v_ne_559_ == 0 {
                    leanh::lean_dec_ref(v_mkNeProof_560_);
                    v___x_570_ = l_Lean_Expr_appFn_x21(v_e_558_);
                    v___x_571_ = l_Lean_Expr_appFn_x21(v___x_570_);
                    v_00_u03b1_572_ = l_Lean_Expr_appArg_x21(v___x_571_);
                    v_a_573_ = l_Lean_Expr_appArg_x21(v___x_570_);
                    leanh::lean_dec_ref(v___x_570_);
                    v___x_574_ = leanh::lean_box(0);
                    v___x_575_ = l_Lean_Expr_appFn_x21(v___x_571_);
                    leanh::lean_dec_ref(v___x_571_);
                    v___x_576_ = l_Lean_Expr_constLevels_x21(v___x_575_);
                    leanh::lean_dec_ref(v___x_575_);
                    v_u_577_ = l_List_head_x21___redArg(v___x_574_, v___x_576_);
                    leanh::lean_dec(v___x_576_);
                    v___x_578_ = l_Lean_Meta_Simp_evalNePropStep___closed__0;
                    v___x_579_ = leanh::lean_box(0);
                    v___x_580_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_580_, 0, v_u_577_);
                    leanh::lean_ctor_set(v___x_580_, 1, v___x_579_);
                    leanh::lean_inc_ref(v___x_580_);
                    v___x_581_ = l_Lean_mkConst(v___x_578_, v___x_580_);
                    leanh::lean_inc_ref_n(v_a_573_, 2);
                    leanh::lean_inc_ref(v_00_u03b1_572_);
                    v_eqProp_582_ = l_Lean_mkApp3(v___x_581_, v_00_u03b1_572_, v_a_573_, v_a_573_);
                    v___x_583_ = l_Lean_Meta_Simp_evalEqPropStep___closed__8;
                    v___x_584_ = l_Lean_mkConst(v___x_583_, v___x_580_);
                    v_rflExpr_585_ = l_Lean_mkAppB(v___x_584_, v_00_u03b1_572_, v_a_573_);
                    v___x_586_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2_once),
                        _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2,
                    );
                    v___x_587_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalNePropStep___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalNePropStep___closed__3_once),
                        _init_l_Lean_Meta_Simp_evalNePropStep___closed__3,
                    );
                    v___x_588_ = l_Lean_mkAppB(v___x_587_, v_eqProp_582_, v_rflExpr_585_);
                    v_proof_589_ = l_Lean_mkAppB(v___x_586_, v_e_558_, v___x_588_);
                    v___x_590_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once
                        ),
                        _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6,
                    );
                    v___x_591_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_591_, 0, v_proof_589_);
                    v___x_592_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_592_, 0, v___x_590_);
                    leanh::lean_ctor_set(v___x_592_, 1, v___x_591_);
                    leanh::lean_ctor_set_uint8(
                        v___x_592_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_569_,
                    );
                    v___x_593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_593_, 0, v___x_592_);
                    v___x_594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_594_, 0, v___x_593_);
                    return v___x_594_;
                } else {
                    leanh::lean_inc(v_a_567_);
                    leanh::lean_inc_ref(v_a_566_);
                    leanh::lean_inc(v_a_565_);
                    leanh::lean_inc_ref(v_a_564_);
                    leanh::lean_inc(v_a_563_);
                    leanh::lean_inc_ref(v_a_562_);
                    leanh::lean_inc(v_a_561_);
                    v___x_595_ = leanh::lean_apply_8(
                        v_mkNeProof_560_,
                        v_a_561_,
                        v_a_562_,
                        v_a_563_,
                        v_a_564_,
                        v_a_565_,
                        v_a_566_,
                        v_a_567_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_595_) == 0 {
                        v_a_596_ = leanh::lean_ctor_get(v___x_595_, 0);
                        v_isSharedCheck_609_ = (!leanh::lean_is_exclusive(v___x_595_)) as u8;
                        if v_isSharedCheck_609_ == 0 {
                            v___x_598_ = v___x_595_;
                            v_isShared_599_ = v_isSharedCheck_609_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_596_);
                            leanh::lean_dec(v___x_595_);
                            v___x_598_ = leanh::lean_box(0);
                            v_isShared_599_ = v_isSharedCheck_609_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_558_);
                        v_a_610_ = leanh::lean_ctor_get(v___x_595_, 0);
                        v_isSharedCheck_617_ = (!leanh::lean_is_exclusive(v___x_595_)) as u8;
                        if v_isSharedCheck_617_ == 0 {
                            v___x_612_ = v___x_595_;
                            v_isShared_613_ = v_isSharedCheck_617_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_610_);
                            leanh::lean_dec(v___x_595_);
                            v___x_612_ = leanh::lean_box(0);
                            v_isShared_613_ = v_isSharedCheck_617_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_600_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5_once),
                    _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5,
                );
                v___x_601_ = l_Lean_mkAppB(v___x_600_, v_e_558_, v_a_596_);
                v___x_602_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15,
                );
                v___x_603_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_603_, 0, v___x_601_);
                v___x_604_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_604_, 0, v___x_602_);
                leanh::lean_ctor_set(v___x_604_, 1, v___x_603_);
                leanh::lean_ctor_set_uint8(
                    v___x_604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_569_,
                );
                v___x_605_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_605_, 0, v___x_604_);
                if v_isShared_599_ == 0 {
                    leanh::lean_ctor_set(v___x_598_, 0, v___x_605_);
                    v___x_607_ = v___x_598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
                    v___x_607_ = v_reuseFailAlloc_608_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_607_;
            }
            3 => {
                if v_isShared_613_ == 0 {
                    v___x_615_ = v___x_612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
                    v___x_615_ = v_reuseFailAlloc_616_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_evalNePropStep___boxed(
    mut v_e_618_: *mut leanh::LeanObject,
    mut v_ne_619_: *mut leanh::LeanObject,
    mut v_mkNeProof_620_: *mut leanh::LeanObject,
    mut v_a_621_: *mut leanh::LeanObject,
    mut v_a_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ne_boxed_629_: u8 = 0;
    let mut v_res_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ne_boxed_629_ = (leanh::lean_unbox(v_ne_619_) as u8);
    v_res_630_ = l_Lean_Meta_Simp_evalNePropStep(
        v_e_618_,
        v_ne_boxed_629_,
        v_mkNeProof_620_,
        v_a_621_,
        v_a_622_,
        v_a_623_,
        v_a_624_,
        v_a_625_,
        v_a_626_,
        v_a_627_,
    );
    leanh::lean_dec(v_a_627_);
    leanh::lean_dec_ref(v_a_626_);
    leanh::lean_dec(v_a_625_);
    leanh::lean_dec_ref(v_a_624_);
    leanh::lean_dec(v_a_623_);
    leanh::lean_dec_ref(v_a_622_);
    leanh::lean_dec(v_a_621_);
    return v_res_630_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
}