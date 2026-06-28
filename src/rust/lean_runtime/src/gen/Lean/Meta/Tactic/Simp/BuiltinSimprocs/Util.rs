// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
// Imports: Lean.Meta.Tactic.Simp.Simproc
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constLevels_x21, l_Lean_mkApp3,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkDecide, l_Lean_Meta_mkEqRefl};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_8, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value)
                as *mut LeanObject,
            15761733860085307253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value)
                as *mut LeanObject,
            907667957179513571 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value)
                as *mut LeanObject,
            4053297232167869867 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value)
                as *mut LeanObject,
            11870096045526947150 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value)
                as *mut LeanObject,
            10755389243347010570 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalPropStep___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__0_value) as *mut LeanObject,
        1953906391527423986 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__3_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__3_value) as *mut LeanObject,
        12633671826946381106 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__6_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__7_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__7_value) as *mut LeanObject;
static l_Lean_Meta_Simp_evalEqPropStep___closed__8_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__6_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_evalEqPropStep___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__8_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__7_value) as *mut LeanObject,
        13480818501600609864 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalEqPropStep___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalNePropStep___closed__0_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalEqPropStep___closed__6_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalNePropStep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalNePropStep___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Simp_evalNePropStep___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Simp_evalNePropStep___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__1_value) as *mut LeanObject,
        5766767816827580045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_evalNePropStep___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_evalNePropStep___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Simp_evalNePropStep___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_evalNePropStep___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_321_ = lean_box(0);
    v___x_322_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__2;
    v___x_323_ = l_Lean_mkConst(v___x_322_, v___x_321_);
    return v___x_323_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_box(0);
    v___x_328_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__5;
    v___x_329_ = l_Lean_mkConst(v___x_328_, v___x_327_);
    return v___x_329_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v___x_333_ = lean_box(0);
    v___x_334_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__8;
    v___x_335_ = l_Lean_mkConst(v___x_334_, v___x_333_);
    return v___x_335_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = lean_box(0);
    v___x_341_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__11;
    v___x_342_ = l_Lean_mkConst(v___x_341_, v___x_340_);
    return v___x_342_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v___x_346_ = lean_box(0);
    v___x_347_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__14;
    v___x_348_ = l_Lean_mkConst(v___x_347_, v___x_346_);
    return v___x_348_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18() -> *mut LeanObject {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_352_ = lean_box(0);
    v___x_353_ = l_Lean_Meta_Simp_evalPropStep___redArg___closed__17;
    v___x_354_ = l_Lean_mkConst(v___x_353_, v___x_352_);
    return v___x_354_;
}
pub unsafe fn l_Lean_Meta_Simp_evalPropStep___redArg(
    mut v_p_355_: *mut LeanObject,
    mut v_result_356_: u8,
    mut v_a_357_: *mut LeanObject,
    mut v_a_358_: *mut LeanObject,
    mut v_a_359_: *mut LeanObject,
    mut v_a_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: u8 = 0;
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v_a_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_390_: u8 = 0;
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_394_: u8 = 0;
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_400_: u8 = 0;
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut v_a_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_420_: u8 = 0;
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut v_a_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_428_: u8 = 0;
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_p_355_);
                v___x_362_ = l_Lean_Meta_mkDecide(v_p_355_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
                if lean_obj_tag(v___x_362_) == 0 {
                    v_a_363_ = lean_ctor_get(v___x_362_, 0);
                    lean_inc(v_a_363_);
                    lean_dec_ref_known(v___x_362_, 1);
                    v___x_364_ = 1;
                    if v_result_356_ == 0 {
                        v___x_365_ = lean_obj_once(
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
                        if lean_obj_tag(v___x_366_) == 0 {
                            v_a_367_ = lean_ctor_get(v___x_366_, 0);
                            v_isSharedCheck_386_ = (!lean_is_exclusive(v___x_366_)) as u8;
                            if v_isSharedCheck_386_ == 0 {
                                v___x_369_ = v___x_366_;
                                v_isShared_370_ = v_isSharedCheck_386_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_367_);
                                lean_dec(v___x_366_);
                                v___x_369_ = lean_box(0);
                                v_isShared_370_ = v_isSharedCheck_386_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_363_);
                            lean_dec_ref(v_p_355_);
                            v_a_387_ = lean_ctor_get(v___x_366_, 0);
                            v_isSharedCheck_394_ = (!lean_is_exclusive(v___x_366_)) as u8;
                            if v_isSharedCheck_394_ == 0 {
                                v___x_389_ = v___x_366_;
                                v_isShared_390_ = v_isSharedCheck_394_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_387_);
                                lean_dec(v___x_366_);
                                v___x_389_ = lean_box(0);
                                v_isShared_390_ = v_isSharedCheck_394_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_395_ = lean_obj_once(
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
                        if lean_obj_tag(v___x_396_) == 0 {
                            v_a_397_ = lean_ctor_get(v___x_396_, 0);
                            v_isSharedCheck_416_ = (!lean_is_exclusive(v___x_396_)) as u8;
                            if v_isSharedCheck_416_ == 0 {
                                v___x_399_ = v___x_396_;
                                v_isShared_400_ = v_isSharedCheck_416_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_397_);
                                lean_dec(v___x_396_);
                                v___x_399_ = lean_box(0);
                                v_isShared_400_ = v_isSharedCheck_416_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_363_);
                            lean_dec_ref(v_p_355_);
                            v_a_417_ = lean_ctor_get(v___x_396_, 0);
                            v_isSharedCheck_424_ = (!lean_is_exclusive(v___x_396_)) as u8;
                            if v_isSharedCheck_424_ == 0 {
                                v___x_419_ = v___x_396_;
                                v_isShared_420_ = v_isSharedCheck_424_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_417_);
                                lean_dec(v___x_396_);
                                v___x_419_ = lean_box(0);
                                v_isShared_420_ = v_isSharedCheck_424_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_p_355_);
                    v_a_425_ = lean_ctor_get(v___x_362_, 0);
                    v_isSharedCheck_432_ = (!lean_is_exclusive(v___x_362_)) as u8;
                    if v_isSharedCheck_432_ == 0 {
                        v___x_427_ = v___x_362_;
                        v_isShared_428_ = v_isSharedCheck_432_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_425_);
                        lean_dec(v___x_362_);
                        v___x_427_ = lean_box(0);
                        v_isShared_428_ = v_isSharedCheck_432_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_371_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6,
                );
                v___x_372_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9,
                );
                v___x_373_ = l_Lean_Expr_appArg_x21(v_a_363_);
                lean_dec(v_a_363_);
                v___x_374_ = lean_unsigned_to_nat(3);
                v___x_375_ = lean_mk_empty_array_with_capacity(v___x_374_);
                v___x_376_ = lean_array_push(v___x_375_, v_p_355_);
                v___x_377_ = lean_array_push(v___x_376_, v___x_373_);
                v___x_378_ = lean_array_push(v___x_377_, v_a_367_);
                v___x_379_ = l_Lean_mkAppN(v___x_372_, v___x_378_);
                lean_dec_ref(v___x_378_);
                v___x_380_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_380_, 0, v___x_379_);
                v___x_381_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_381_, 0, v___x_371_);
                lean_ctor_set(v___x_381_, 1, v___x_380_);
                lean_ctor_set_uint8(
                    v___x_381_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_364_,
                );
                v___x_382_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_382_, 0, v___x_381_);
                if v_isShared_370_ == 0 {
                    lean_ctor_set(v___x_369_, 0, v___x_382_);
                    v___x_384_ = v___x_369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
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
                    v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
                    v___x_392_ = v_reuseFailAlloc_393_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_392_;
            }
            5 => {
                v___x_401_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15,
                );
                v___x_402_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__18),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18,
                );
                v___x_403_ = l_Lean_Expr_appArg_x21(v_a_363_);
                lean_dec(v_a_363_);
                v___x_404_ = lean_unsigned_to_nat(3);
                v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
                v___x_406_ = lean_array_push(v___x_405_, v_p_355_);
                v___x_407_ = lean_array_push(v___x_406_, v___x_403_);
                v___x_408_ = lean_array_push(v___x_407_, v_a_397_);
                v___x_409_ = l_Lean_mkAppN(v___x_402_, v___x_408_);
                lean_dec_ref(v___x_408_);
                v___x_410_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_410_, 0, v___x_409_);
                v___x_411_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_411_, 0, v___x_401_);
                lean_ctor_set(v___x_411_, 1, v___x_410_);
                lean_ctor_set_uint8(
                    v___x_411_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_364_,
                );
                v___x_412_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_412_, 0, v___x_411_);
                if v_isShared_400_ == 0 {
                    lean_ctor_set(v___x_399_, 0, v___x_412_);
                    v___x_414_ = v___x_399_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
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
                    v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
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
                    v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
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
    mut v_p_433_: *mut LeanObject,
    mut v_result_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_result_boxed_440_: u8 = 0;
    let mut v_res_441_: *mut LeanObject = core::ptr::null_mut();
    v_result_boxed_440_ = (lean_unbox(v_result_434_) as u8);
    v_res_441_ = l_Lean_Meta_Simp_evalPropStep___redArg(
        v_p_433_,
        v_result_boxed_440_,
        v_a_435_,
        v_a_436_,
        v_a_437_,
        v_a_438_,
    );
    lean_dec(v_a_438_);
    lean_dec_ref(v_a_437_);
    lean_dec(v_a_436_);
    lean_dec_ref(v_a_435_);
    return v_res_441_;
}
pub unsafe fn l_Lean_Meta_Simp_evalPropStep(
    mut v_p_442_: *mut LeanObject,
    mut v_result_443_: u8,
    mut v_a_444_: *mut LeanObject,
    mut v_a_445_: *mut LeanObject,
    mut v_a_446_: *mut LeanObject,
    mut v_a_447_: *mut LeanObject,
    mut v_a_448_: *mut LeanObject,
    mut v_a_449_: *mut LeanObject,
    mut v_a_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_p_453_: *mut LeanObject,
    mut v_result_454_: *mut LeanObject,
    mut v_a_455_: *mut LeanObject,
    mut v_a_456_: *mut LeanObject,
    mut v_a_457_: *mut LeanObject,
    mut v_a_458_: *mut LeanObject,
    mut v_a_459_: *mut LeanObject,
    mut v_a_460_: *mut LeanObject,
    mut v_a_461_: *mut LeanObject,
    mut v_a_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_result_boxed_463_: u8 = 0;
    let mut v_res_464_: *mut LeanObject = core::ptr::null_mut();
    v_result_boxed_463_ = (lean_unbox(v_result_454_) as u8);
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
    lean_dec(v_a_461_);
    lean_dec_ref(v_a_460_);
    lean_dec(v_a_459_);
    lean_dec_ref(v_a_458_);
    lean_dec(v_a_457_);
    lean_dec_ref(v_a_456_);
    lean_dec(v_a_455_);
    return v_res_464_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2() -> *mut LeanObject {
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_468_ = lean_box(0);
    v___x_469_ = l_Lean_Meta_Simp_evalEqPropStep___closed__1;
    v___x_470_ = l_Lean_mkConst(v___x_469_, v___x_468_);
    return v___x_470_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5() -> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_box(0);
    v___x_475_ = l_Lean_Meta_Simp_evalEqPropStep___closed__4;
    v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_474_);
    return v___x_476_;
}
pub unsafe fn l_Lean_Meta_Simp_evalEqPropStep(
    mut v_e_482_: *mut LeanObject,
    mut v_eq_483_: u8,
    mut v_mkNeProof_484_: *mut LeanObject,
    mut v_a_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
    mut v_a_489_: *mut LeanObject,
    mut v_a_490_: *mut LeanObject,
    mut v_a_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_493_: u8 = 0;
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut v_a_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_493_ = 1;
                if v_eq_483_ == 0 {
                    lean_inc(v_a_491_);
                    lean_inc_ref(v_a_490_);
                    lean_inc(v_a_489_);
                    lean_inc_ref(v_a_488_);
                    lean_inc(v_a_487_);
                    lean_inc_ref(v_a_486_);
                    lean_inc(v_a_485_);
                    v___x_494_ = lean_apply_8(
                        v_mkNeProof_484_,
                        v_a_485_,
                        v_a_486_,
                        v_a_487_,
                        v_a_488_,
                        v_a_489_,
                        v_a_490_,
                        v_a_491_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_494_) == 0 {
                        v_a_495_ = lean_ctor_get(v___x_494_, 0);
                        v_isSharedCheck_508_ = (!lean_is_exclusive(v___x_494_)) as u8;
                        if v_isSharedCheck_508_ == 0 {
                            v___x_497_ = v___x_494_;
                            v_isShared_498_ = v_isSharedCheck_508_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_495_);
                            lean_dec(v___x_494_);
                            v___x_497_ = lean_box(0);
                            v_isShared_498_ = v_isSharedCheck_508_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_482_);
                        v_a_509_ = lean_ctor_get(v___x_494_, 0);
                        v_isSharedCheck_516_ = (!lean_is_exclusive(v___x_494_)) as u8;
                        if v_isSharedCheck_516_ == 0 {
                            v___x_511_ = v___x_494_;
                            v_isShared_512_ = v_isSharedCheck_516_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_509_);
                            lean_dec(v___x_494_);
                            v___x_511_ = lean_box(0);
                            v_isShared_512_ = v_isSharedCheck_516_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_mkNeProof_484_);
                    v___x_517_ = lean_box(0);
                    v___x_518_ = l_Lean_Expr_appFn_x21(v_e_482_);
                    v___x_519_ = l_Lean_Expr_appFn_x21(v___x_518_);
                    v_00_u03b1_520_ = l_Lean_Expr_appArg_x21(v___x_519_);
                    v_a_521_ = l_Lean_Expr_appArg_x21(v___x_518_);
                    lean_dec_ref(v___x_518_);
                    v___x_522_ = l_Lean_Expr_appFn_x21(v___x_519_);
                    lean_dec_ref(v___x_519_);
                    v___x_523_ = l_Lean_Expr_constLevels_x21(v___x_522_);
                    lean_dec_ref(v___x_522_);
                    v_u_524_ = l_List_head_x21___redArg(v___x_517_, v___x_523_);
                    lean_dec(v___x_523_);
                    v___x_525_ = lean_box(0);
                    v___x_526_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5_once),
                        _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5,
                    );
                    v___x_527_ = l_Lean_Meta_Simp_evalEqPropStep___closed__8;
                    v___x_528_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_528_, 0, v_u_524_);
                    lean_ctor_set(v___x_528_, 1, v___x_525_);
                    v___x_529_ = l_Lean_mkConst(v___x_527_, v___x_528_);
                    v___x_530_ = l_Lean_mkAppB(v___x_529_, v_00_u03b1_520_, v_a_521_);
                    v_proof_531_ = l_Lean_mkAppB(v___x_526_, v_e_482_, v___x_530_);
                    v___x_532_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_evalPropStep___redArg___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once
                        ),
                        _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15,
                    );
                    v___x_533_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_533_, 0, v_proof_531_);
                    v___x_534_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_534_, 0, v___x_532_);
                    lean_ctor_set(v___x_534_, 1, v___x_533_);
                    lean_ctor_set_uint8(
                        v___x_534_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_493_,
                    );
                    v___x_535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_535_, 0, v___x_534_);
                    v___x_536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_536_, 0, v___x_535_);
                    return v___x_536_;
                }
            }
            1 => {
                v___x_499_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2_once),
                    _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2,
                );
                v___x_500_ = l_Lean_mkAppB(v___x_499_, v_e_482_, v_a_495_);
                v___x_501_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6,
                );
                v___x_502_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_502_, 0, v___x_500_);
                v___x_503_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_503_, 0, v___x_501_);
                lean_ctor_set(v___x_503_, 1, v___x_502_);
                lean_ctor_set_uint8(
                    v___x_503_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_493_,
                );
                v___x_504_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_504_, 0, v___x_503_);
                if v_isShared_498_ == 0 {
                    lean_ctor_set(v___x_497_, 0, v___x_504_);
                    v___x_506_ = v___x_497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
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
                    v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
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
    mut v_e_537_: *mut LeanObject,
    mut v_eq_538_: *mut LeanObject,
    mut v_mkNeProof_539_: *mut LeanObject,
    mut v_a_540_: *mut LeanObject,
    mut v_a_541_: *mut LeanObject,
    mut v_a_542_: *mut LeanObject,
    mut v_a_543_: *mut LeanObject,
    mut v_a_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
    mut v_a_547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_boxed_548_: u8 = 0;
    let mut v_res_549_: *mut LeanObject = core::ptr::null_mut();
    v_eq_boxed_548_ = (lean_unbox(v_eq_538_) as u8);
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
    lean_dec(v_a_546_);
    lean_dec_ref(v_a_545_);
    lean_dec(v_a_544_);
    lean_dec_ref(v_a_543_);
    lean_dec(v_a_542_);
    lean_dec_ref(v_a_541_);
    lean_dec(v_a_540_);
    return v_res_549_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_evalNePropStep___closed__3() -> *mut LeanObject {
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    v___x_555_ = lean_box(0);
    v___x_556_ = l_Lean_Meta_Simp_evalNePropStep___closed__2;
    v___x_557_ = l_Lean_mkConst(v___x_556_, v___x_555_);
    return v___x_557_;
}
pub unsafe fn l_Lean_Meta_Simp_evalNePropStep(
    mut v_e_558_: *mut LeanObject,
    mut v_ne_559_: u8,
    mut v_mkNeProof_560_: *mut LeanObject,
    mut v_a_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
    mut v_a_563_: *mut LeanObject,
    mut v_a_564_: *mut LeanObject,
    mut v_a_565_: *mut LeanObject,
    mut v_a_566_: *mut LeanObject,
    mut v_a_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03b1_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProp_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rflExpr_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_609_: u8 = 0;
    let mut v_a_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_613_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_569_ = 1;
                if v_ne_559_ == 0 {
                    lean_dec_ref(v_mkNeProof_560_);
                    v___x_570_ = l_Lean_Expr_appFn_x21(v_e_558_);
                    v___x_571_ = l_Lean_Expr_appFn_x21(v___x_570_);
                    v_00_u03b1_572_ = l_Lean_Expr_appArg_x21(v___x_571_);
                    v_a_573_ = l_Lean_Expr_appArg_x21(v___x_570_);
                    lean_dec_ref(v___x_570_);
                    v___x_574_ = lean_box(0);
                    v___x_575_ = l_Lean_Expr_appFn_x21(v___x_571_);
                    lean_dec_ref(v___x_571_);
                    v___x_576_ = l_Lean_Expr_constLevels_x21(v___x_575_);
                    lean_dec_ref(v___x_575_);
                    v_u_577_ = l_List_head_x21___redArg(v___x_574_, v___x_576_);
                    lean_dec(v___x_576_);
                    v___x_578_ = l_Lean_Meta_Simp_evalNePropStep___closed__0;
                    v___x_579_ = lean_box(0);
                    v___x_580_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_580_, 0, v_u_577_);
                    lean_ctor_set(v___x_580_, 1, v___x_579_);
                    lean_inc_ref(v___x_580_);
                    v___x_581_ = l_Lean_mkConst(v___x_578_, v___x_580_);
                    lean_inc_ref_n(v_a_573_, 2);
                    lean_inc_ref(v_00_u03b1_572_);
                    v_eqProp_582_ = l_Lean_mkApp3(v___x_581_, v_00_u03b1_572_, v_a_573_, v_a_573_);
                    v___x_583_ = l_Lean_Meta_Simp_evalEqPropStep___closed__8;
                    v___x_584_ = l_Lean_mkConst(v___x_583_, v___x_580_);
                    v_rflExpr_585_ = l_Lean_mkAppB(v___x_584_, v_00_u03b1_572_, v_a_573_);
                    v___x_586_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__2_once),
                        _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2,
                    );
                    v___x_587_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalNePropStep___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalNePropStep___closed__3_once),
                        _init_l_Lean_Meta_Simp_evalNePropStep___closed__3,
                    );
                    v___x_588_ = l_Lean_mkAppB(v___x_587_, v_eqProp_582_, v_rflExpr_585_);
                    v_proof_589_ = l_Lean_mkAppB(v___x_586_, v_e_558_, v___x_588_);
                    v___x_590_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once
                        ),
                        _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6,
                    );
                    v___x_591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_591_, 0, v_proof_589_);
                    v___x_592_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_592_, 0, v___x_590_);
                    lean_ctor_set(v___x_592_, 1, v___x_591_);
                    lean_ctor_set_uint8(
                        v___x_592_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_569_,
                    );
                    v___x_593_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_593_, 0, v___x_592_);
                    v___x_594_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_594_, 0, v___x_593_);
                    return v___x_594_;
                } else {
                    lean_inc(v_a_567_);
                    lean_inc_ref(v_a_566_);
                    lean_inc(v_a_565_);
                    lean_inc_ref(v_a_564_);
                    lean_inc(v_a_563_);
                    lean_inc_ref(v_a_562_);
                    lean_inc(v_a_561_);
                    v___x_595_ = lean_apply_8(
                        v_mkNeProof_560_,
                        v_a_561_,
                        v_a_562_,
                        v_a_563_,
                        v_a_564_,
                        v_a_565_,
                        v_a_566_,
                        v_a_567_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_595_) == 0 {
                        v_a_596_ = lean_ctor_get(v___x_595_, 0);
                        v_isSharedCheck_609_ = (!lean_is_exclusive(v___x_595_)) as u8;
                        if v_isSharedCheck_609_ == 0 {
                            v___x_598_ = v___x_595_;
                            v_isShared_599_ = v_isSharedCheck_609_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_596_);
                            lean_dec(v___x_595_);
                            v___x_598_ = lean_box(0);
                            v_isShared_599_ = v_isSharedCheck_609_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_558_);
                        v_a_610_ = lean_ctor_get(v___x_595_, 0);
                        v_isSharedCheck_617_ = (!lean_is_exclusive(v___x_595_)) as u8;
                        if v_isSharedCheck_617_ == 0 {
                            v___x_612_ = v___x_595_;
                            v_isShared_613_ = v_isSharedCheck_617_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_610_);
                            lean_dec(v___x_595_);
                            v___x_612_ = lean_box(0);
                            v_isShared_613_ = v_isSharedCheck_617_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_600_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalEqPropStep___closed__5_once),
                    _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5,
                );
                v___x_601_ = l_Lean_mkAppB(v___x_600_, v_e_558_, v_a_596_);
                v___x_602_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_evalPropStep___redArg___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once
                    ),
                    _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15,
                );
                v___x_603_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_603_, 0, v___x_601_);
                v___x_604_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_604_, 0, v___x_602_);
                lean_ctor_set(v___x_604_, 1, v___x_603_);
                lean_ctor_set_uint8(
                    v___x_604_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_569_,
                );
                v___x_605_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_605_, 0, v___x_604_);
                if v_isShared_599_ == 0 {
                    lean_ctor_set(v___x_598_, 0, v___x_605_);
                    v___x_607_ = v___x_598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
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
                    v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
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
    mut v_e_618_: *mut LeanObject,
    mut v_ne_619_: *mut LeanObject,
    mut v_mkNeProof_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
    mut v_a_622_: *mut LeanObject,
    mut v_a_623_: *mut LeanObject,
    mut v_a_624_: *mut LeanObject,
    mut v_a_625_: *mut LeanObject,
    mut v_a_626_: *mut LeanObject,
    mut v_a_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ne_boxed_629_: u8 = 0;
    let mut v_res_630_: *mut LeanObject = core::ptr::null_mut();
    v_ne_boxed_629_ = (lean_unbox(v_ne_619_) as u8);
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
    lean_dec(v_a_627_);
    lean_dec_ref(v_a_626_);
    lean_dec(v_a_625_);
    lean_dec_ref(v_a_624_);
    lean_dec(v_a_623_);
    lean_dec_ref(v_a_622_);
    lean_dec(v_a_621_);
    return v_res_630_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
}
