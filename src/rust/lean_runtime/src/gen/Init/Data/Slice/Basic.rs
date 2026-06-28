// Lean compiler output
// Module: Init.Data.Slice.Basic
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
};
pub static l_Std_Slice_Self_eq___autoParam___closed__0_value: LeanStringObject<5> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__0_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__1_value: LeanStringObject<7> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__1_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__2_value: LeanStringObject<7> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__2_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__3_value: LeanStringObject<10> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__3_value) as *mut LeanObject;
static l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Slice_Self_eq___autoParam___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Std_Slice_Self_eq___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__4_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Std_Slice_Self_eq___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__5_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__6_value: LeanStringObject<19> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__6_value) as *mut LeanObject;
static l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Slice_Self_eq___autoParam___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__7_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Std_Slice_Self_eq___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__7_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__8_value: LeanStringObject<5> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__8_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Std_Slice_Self_eq___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__9_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__10_value: LeanStringObject<10> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__10_value) as *mut LeanObject;
static l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Slice_Self_eq___autoParam___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__11_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__10_value) as *mut LeanObject,
        3294379458557754569 as *mut LeanObject,
    ],
};
static mut l_Std_Slice_Self_eq___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__11_value) as *mut LeanObject;
pub static l_Std_Slice_Self_eq___autoParam___closed__12_value: LeanStringObject<4> =
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
static mut l_Std_Slice_Self_eq___autoParam___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_Self_eq___autoParam___closed__12_value) as *mut LeanObject;
static mut l_Std_Slice_Self_eq___autoParam___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Slice_Self_eq___autoParam___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Slice_Self_eq___autoParam___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Slice_Self_eq___autoParam: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__13() -> *mut LeanObject {
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
    v___x_86_ = l_Std_Slice_Self_eq___autoParam___closed__12;
    v___x_87_ = l_Lean_mkAtom(v___x_86_);
    return v___x_87_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__14() -> *mut LeanObject {
    let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
    v___x_88_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__13_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__13,
    );
    v___x_89_ = l_Std_Slice_Self_eq___autoParam___closed__5;
    v___x_90_ = lean_array_push(v___x_89_, v___x_88_);
    return v___x_90_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__15() -> *mut LeanObject {
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
    v___x_91_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__14_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__14,
    );
    v___x_92_ = l_Std_Slice_Self_eq___autoParam___closed__11;
    v___x_93_ = lean_box(2);
    v___x_94_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_94_, 0, v___x_93_);
    lean_ctor_set(v___x_94_, 1, v___x_92_);
    lean_ctor_set(v___x_94_, 2, v___x_91_);
    return v___x_94_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__16() -> *mut LeanObject {
    let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    v___x_95_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__15_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__15,
    );
    v___x_96_ = l_Std_Slice_Self_eq___autoParam___closed__5;
    v___x_97_ = lean_array_push(v___x_96_, v___x_95_);
    return v___x_97_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__17() -> *mut LeanObject {
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    v___x_98_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__16_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__16,
    );
    v___x_99_ = l_Std_Slice_Self_eq___autoParam___closed__9;
    v___x_100_ = lean_box(2);
    v___x_101_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_101_, 0, v___x_100_);
    lean_ctor_set(v___x_101_, 1, v___x_99_);
    lean_ctor_set(v___x_101_, 2, v___x_98_);
    return v___x_101_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__18() -> *mut LeanObject {
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    v___x_102_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__17_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__17,
    );
    v___x_103_ = l_Std_Slice_Self_eq___autoParam___closed__5;
    v___x_104_ = lean_array_push(v___x_103_, v___x_102_);
    return v___x_104_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__19() -> *mut LeanObject {
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    v___x_105_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__18_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__18,
    );
    v___x_106_ = l_Std_Slice_Self_eq___autoParam___closed__7;
    v___x_107_ = lean_box(2);
    v___x_108_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_108_, 0, v___x_107_);
    lean_ctor_set(v___x_108_, 1, v___x_106_);
    lean_ctor_set(v___x_108_, 2, v___x_105_);
    return v___x_108_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__20() -> *mut LeanObject {
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
    v___x_109_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__19_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__19,
    );
    v___x_110_ = l_Std_Slice_Self_eq___autoParam___closed__5;
    v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
    return v___x_111_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam___closed__21() -> *mut LeanObject {
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    v___x_112_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__20_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__20,
    );
    v___x_113_ = l_Std_Slice_Self_eq___autoParam___closed__4;
    v___x_114_ = lean_box(2);
    v___x_115_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_115_, 0, v___x_114_);
    lean_ctor_set(v___x_115_, 1, v___x_113_);
    lean_ctor_set(v___x_115_, 2, v___x_112_);
    return v___x_115_;
}
pub unsafe fn _init_l_Std_Slice_Self_eq___autoParam() -> *mut LeanObject {
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    v___x_116_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Std_Slice_Self_eq___autoParam___closed__21_once),
        _init_l_Std_Slice_Self_eq___autoParam___closed__21,
    );
    return v___x_116_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Slice_Self_eq___autoParam = _init_l_Std_Slice_Self_eq___autoParam();
    lean_mark_persistent(l_Std_Slice_Self_eq___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Slice_Basic(builtin);
}
