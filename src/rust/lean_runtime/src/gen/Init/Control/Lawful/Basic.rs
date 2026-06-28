// Lean compiler output
// Module: Init.Control.Lawful.Basic
// Imports: Init.Control.Id Init.Grind.Tactics Init.Ext
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, runtime_initialize_Init_Control_Id,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
};
pub static l_LawfulMonad_mk_x27___auto__1___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_LawfulMonad_mk_x27___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__3_value) as *mut LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_LawfulMonad_mk_x27___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__4_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__5_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__6_value: LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__6_value) as *mut LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_LawfulMonad_mk_x27___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__7_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__8_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__9_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__10_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 116, 114, 111, 115, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__10_value) as *mut LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_LawfulMonad_mk_x27___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__10_value) as *mut LeanObject,
        3278676588586250010 as *mut LeanObject,
    ],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__11_value) as *mut LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_LawfulMonad_mk_x27___auto__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__14_value) as *mut LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_LawfulMonad_mk_x27___auto__1___closed__18_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [59, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__18_value) as *mut LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l_LawfulMonad_mk_x27___auto__1___closed__21_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__21_value) as *mut LeanObject;
static l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_LawfulMonad_mk_x27___auto__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__21_value) as *mut LeanObject,
        3294379458557754569 as *mut LeanObject,
    ],
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__22_value) as *mut LeanObject;
pub static l_LawfulMonad_mk_x27___auto__1___closed__23_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [114, 102, 108, 0],
    };
static mut l_LawfulMonad_mk_x27___auto__1___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_LawfulMonad_mk_x27___auto__1___closed__23_value) as *mut LeanObject;
static mut l_LawfulMonad_mk_x27___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__27: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__31: *mut LeanObject = core::ptr::null_mut();
static mut l_LawfulMonad_mk_x27___auto__1___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_LawfulMonad_mk_x27___auto__1___closed__32: *mut LeanObject = core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_LawfulMonad_mk_x27___auto__9: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    v___x_120_ = l_LawfulMonad_mk_x27___auto__1___closed__10;
    v___x_121_ = l_Lean_mkAtom(v___x_120_);
    return v___x_121_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
    v___x_122_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__12_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__12,
    );
    v___x_123_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_124_ = lean_array_push(v___x_123_, v___x_122_);
    return v___x_124_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    v___x_129_ = l_LawfulMonad_mk_x27___auto__1___closed__14;
    v___x_130_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__13_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__13,
    );
    v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
    return v___x_131_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    v___x_132_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__15_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__15,
    );
    v___x_133_ = l_LawfulMonad_mk_x27___auto__1___closed__11;
    v___x_134_ = lean_box(2);
    v___x_135_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_135_, 0, v___x_134_);
    lean_ctor_set(v___x_135_, 1, v___x_133_);
    lean_ctor_set(v___x_135_, 2, v___x_132_);
    return v___x_135_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    v___x_136_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__16_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__16,
    );
    v___x_137_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_138_ = lean_array_push(v___x_137_, v___x_136_);
    return v___x_138_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
    v___x_140_ = l_LawfulMonad_mk_x27___auto__1___closed__18;
    v___x_141_ = l_Lean_mkAtom(v___x_140_);
    return v___x_141_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
    v___x_142_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__19_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__19,
    );
    v___x_143_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__17_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__17,
    );
    v___x_144_ = lean_array_push(v___x_143_, v___x_142_);
    return v___x_144_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    v___x_152_ = l_LawfulMonad_mk_x27___auto__1___closed__23;
    v___x_153_ = l_Lean_mkAtom(v___x_152_);
    return v___x_153_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    v___x_154_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__24_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__24,
    );
    v___x_155_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_156_ = lean_array_push(v___x_155_, v___x_154_);
    return v___x_156_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    v___x_157_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__25_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__25,
    );
    v___x_158_ = l_LawfulMonad_mk_x27___auto__1___closed__22;
    v___x_159_ = lean_box(2);
    v___x_160_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_160_, 0, v___x_159_);
    lean_ctor_set(v___x_160_, 1, v___x_158_);
    lean_ctor_set(v___x_160_, 2, v___x_157_);
    return v___x_160_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    v___x_161_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__26_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__26,
    );
    v___x_162_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__20_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__20,
    );
    v___x_163_ = lean_array_push(v___x_162_, v___x_161_);
    return v___x_163_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    v___x_164_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__27_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__27,
    );
    v___x_165_ = l_LawfulMonad_mk_x27___auto__1___closed__9;
    v___x_166_ = lean_box(2);
    v___x_167_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_167_, 0, v___x_166_);
    lean_ctor_set(v___x_167_, 1, v___x_165_);
    lean_ctor_set(v___x_167_, 2, v___x_164_);
    return v___x_167_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__28_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__28,
    );
    v___x_169_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_170_ = lean_array_push(v___x_169_, v___x_168_);
    return v___x_170_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__30() -> *mut LeanObject {
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    v___x_171_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__29_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__29,
    );
    v___x_172_ = l_LawfulMonad_mk_x27___auto__1___closed__7;
    v___x_173_ = lean_box(2);
    v___x_174_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_174_, 0, v___x_173_);
    lean_ctor_set(v___x_174_, 1, v___x_172_);
    lean_ctor_set(v___x_174_, 2, v___x_171_);
    return v___x_174_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__31() -> *mut LeanObject {
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    v___x_175_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__30_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__30,
    );
    v___x_176_ = l_LawfulMonad_mk_x27___auto__1___closed__5;
    v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
    return v___x_177_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1___closed__32() -> *mut LeanObject {
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    v___x_178_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__31_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__31,
    );
    v___x_179_ = l_LawfulMonad_mk_x27___auto__1___closed__4;
    v___x_180_ = lean_box(2);
    v___x_181_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_181_, 0, v___x_180_);
    lean_ctor_set(v___x_181_, 1, v___x_179_);
    lean_ctor_set(v___x_181_, 2, v___x_178_);
    return v___x_181_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__1() -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    v___x_182_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_182_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__3() -> *mut LeanObject {
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    v___x_183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_183_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__5() -> *mut LeanObject {
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    v___x_184_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_184_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__7() -> *mut LeanObject {
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    v___x_185_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_185_;
}
pub unsafe fn _init_l_LawfulMonad_mk_x27___auto__9() -> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    v___x_186_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_LawfulMonad_mk_x27___auto__1___closed__32_once),
        _init_l_LawfulMonad_mk_x27___auto__1___closed__32,
    );
    return v___x_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Lawful_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Id(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Lawful_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_LawfulMonad_mk_x27___auto__1 = _init_l_LawfulMonad_mk_x27___auto__1();
    lean_mark_persistent(l_LawfulMonad_mk_x27___auto__1);
    l_LawfulMonad_mk_x27___auto__3 = _init_l_LawfulMonad_mk_x27___auto__3();
    lean_mark_persistent(l_LawfulMonad_mk_x27___auto__3);
    l_LawfulMonad_mk_x27___auto__5 = _init_l_LawfulMonad_mk_x27___auto__5();
    lean_mark_persistent(l_LawfulMonad_mk_x27___auto__5);
    l_LawfulMonad_mk_x27___auto__7 = _init_l_LawfulMonad_mk_x27___auto__7();
    lean_mark_persistent(l_LawfulMonad_mk_x27___auto__7);
    l_LawfulMonad_mk_x27___auto__9 = _init_l_LawfulMonad_mk_x27___auto__9();
    lean_mark_persistent(l_LawfulMonad_mk_x27___auto__9);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Lawful_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Id(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Lawful_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Lawful_Basic(builtin);
}
