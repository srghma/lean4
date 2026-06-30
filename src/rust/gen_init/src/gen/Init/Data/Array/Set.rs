// Lean compiler output
// Module: Init.Data.Array.Set
// Imports: Init.Tactics
use crate::ffi::{
    lean_array_fset, lean_array_get_size, lean_array_push, lean_array_set, lean_nat_dec_lt,
};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
pub static l_Array_set___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Array_set___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Array_set___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Array_set___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Array_set___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__3_value) as *mut leanh::LeanObject;
static l_Array_set___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_set___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_set___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_set___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_set___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_set___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_set___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_set___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Array_set___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Array_set___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__6_value) as *mut leanh::LeanObject;
static l_Array_set___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Array_set___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_set___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Array_set___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_set___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Array_set___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_set___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_set___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Array_set___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_set___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__10_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116,
            105, 99, 0,
        ],
    };
static mut l_Array_set___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Array_set___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            3731765604234633101 as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_set___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Array_set___auto__1___closed__12_value: leanh::LeanStringObject<16> =
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
            103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_Array_set___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_set___auto__1___closed__12_value) as *mut leanh::LeanObject;
static mut l_Array_set___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Array_set___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Array_set___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Array_set___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Array_set___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = l_Array_set___auto__1___closed__12;
    v___x_123_ = l_Lean_mkAtom(v___x_122_);
    return v___x_123_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__13_once),
        _init_l_Array_set___auto__1___closed__13,
    );
    v___x_125_ = l_Array_set___auto__1___closed__5;
    v___x_126_ = lean_array_push(v___x_125_, v___x_124_);
    return v___x_126_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_127_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__14_once),
        _init_l_Array_set___auto__1___closed__14,
    );
    v___x_128_ = l_Array_set___auto__1___closed__11;
    v___x_129_ = leanh::lean_box(2);
    v___x_130_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_130_, 0, v___x_129_);
    leanh::lean_ctor_set(v___x_130_, 1, v___x_128_);
    leanh::lean_ctor_set(v___x_130_, 2, v___x_127_);
    return v___x_130_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_131_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__15_once),
        _init_l_Array_set___auto__1___closed__15,
    );
    v___x_132_ = l_Array_set___auto__1___closed__5;
    v___x_133_ = lean_array_push(v___x_132_, v___x_131_);
    return v___x_133_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__16_once),
        _init_l_Array_set___auto__1___closed__16,
    );
    v___x_135_ = l_Array_set___auto__1___closed__9;
    v___x_136_ = leanh::lean_box(2);
    v___x_137_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_137_, 0, v___x_136_);
    leanh::lean_ctor_set(v___x_137_, 1, v___x_135_);
    leanh::lean_ctor_set(v___x_137_, 2, v___x_134_);
    return v___x_137_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_138_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__17_once),
        _init_l_Array_set___auto__1___closed__17,
    );
    v___x_139_ = l_Array_set___auto__1___closed__5;
    v___x_140_ = lean_array_push(v___x_139_, v___x_138_);
    return v___x_140_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__18_once),
        _init_l_Array_set___auto__1___closed__18,
    );
    v___x_142_ = l_Array_set___auto__1___closed__7;
    v___x_143_ = leanh::lean_box(2);
    v___x_144_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_144_, 0, v___x_143_);
    leanh::lean_ctor_set(v___x_144_, 1, v___x_142_);
    leanh::lean_ctor_set(v___x_144_, 2, v___x_141_);
    return v___x_144_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__19_once),
        _init_l_Array_set___auto__1___closed__19,
    );
    v___x_146_ = l_Array_set___auto__1___closed__5;
    v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
    return v___x_147_;
}
pub unsafe fn _init_l_Array_set___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_148_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__20_once),
        _init_l_Array_set___auto__1___closed__20,
    );
    v___x_149_ = l_Array_set___auto__1___closed__4;
    v___x_150_ = leanh::lean_box(2);
    v___x_151_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_151_, 0, v___x_150_);
    leanh::lean_ctor_set(v___x_151_, 1, v___x_149_);
    leanh::lean_ctor_set(v___x_151_, 2, v___x_148_);
    return v___x_151_;
}
pub unsafe fn _init_l_Array_set___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_set___auto__1___closed__21_once),
        _init_l_Array_set___auto__1___closed__21,
    );
    return v___x_152_;
}
pub unsafe fn l_Array_set___boxed(
    mut v_00_u03b1_158_: *mut leanh::LeanObject,
    mut v_xs_159_: *mut leanh::LeanObject,
    mut v_i_160_: *mut leanh::LeanObject,
    mut v_v_161_: *mut leanh::LeanObject,
    mut v_h_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ = lean_array_fset(v_xs_159_, v_i_160_, v_v_161_);
    leanh::lean_dec(v_i_160_);
    return v_res_163_;
}
pub unsafe fn l_Array_setIfInBounds___redArg(
    mut v_xs_164_: *mut leanh::LeanObject,
    mut v_i_165_: *mut leanh::LeanObject,
    mut v_v_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: u8 = 0;
    v___x_167_ = lean_array_get_size(v_xs_164_);
    v___x_168_ = lean_nat_dec_lt(v_i_165_, v___x_167_);
    if v___x_168_ == 0 {
        leanh::lean_dec(v_v_166_);
        return v_xs_164_;
    } else {
        let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_169_ = lean_array_fset(v_xs_164_, v_i_165_, v_v_166_);
        return v___x_169_;
    }
}
pub unsafe fn l_Array_setIfInBounds___redArg___boxed(
    mut v_xs_170_: *mut leanh::LeanObject,
    mut v_i_171_: *mut leanh::LeanObject,
    mut v_v_172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_173_ = l_Array_setIfInBounds___redArg(v_xs_170_, v_i_171_, v_v_172_);
    leanh::lean_dec(v_i_171_);
    return v_res_173_;
}
pub unsafe fn l_Array_setIfInBounds(
    mut v_00_u03b1_174_: *mut leanh::LeanObject,
    mut v_xs_175_: *mut leanh::LeanObject,
    mut v_i_176_: *mut leanh::LeanObject,
    mut v_v_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: u8 = 0;
    v___x_178_ = lean_array_get_size(v_xs_175_);
    v___x_179_ = lean_nat_dec_lt(v_i_176_, v___x_178_);
    if v___x_179_ == 0 {
        leanh::lean_dec(v_v_177_);
        return v_xs_175_;
    } else {
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_180_ = lean_array_fset(v_xs_175_, v_i_176_, v_v_177_);
        return v___x_180_;
    }
}
pub unsafe fn l_Array_setIfInBounds___boxed(
    mut v_00_u03b1_181_: *mut leanh::LeanObject,
    mut v_xs_182_: *mut leanh::LeanObject,
    mut v_i_183_: *mut leanh::LeanObject,
    mut v_v_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_185_ = l_Array_setIfInBounds(v_00_u03b1_181_, v_xs_182_, v_i_183_, v_v_184_);
    leanh::lean_dec(v_i_183_);
    return v_res_185_;
}
pub unsafe fn l_Array_set_x21___boxed(
    mut v_00_u03b1_190_: *mut leanh::LeanObject,
    mut v_xs_191_: *mut leanh::LeanObject,
    mut v_i_192_: *mut leanh::LeanObject,
    mut v_v_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = lean_array_set(v_xs_191_, v_i_192_, v_v_193_);
    leanh::lean_dec(v_i_192_);
    return v_res_194_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Set(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Set(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_set___auto__1 = _init_l_Array_set___auto__1();
    leanh::lean_mark_persistent(l_Array_set___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Set(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Set(builtin);
}