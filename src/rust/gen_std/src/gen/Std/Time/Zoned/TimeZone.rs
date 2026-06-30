// Lean compiler output
// Module: Std.Time.Zoned.TimeZone
// Imports: Std.Time.Zoned.Offset
use crate::ffi::{lean_int_dec_eq, lean_nat_to_int, lean_string_dec_eq, lean_string_length};
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_String_quote};
use crate::r#gen::Std::Time::Zoned::Offset::{
    initialize_Std_Time_Zoned_Offset, l_Std_Time_TimeZone_Offset_ofHours,
    l_Std_Time_TimeZone_Offset_zero, l_Std_Time_TimeZone_instReprOffset_repr___redArg,
    runtime_initialize_Std_Time_Zoned_Offset,
};
static mut l_Std_Time_instInhabitedTimeZone_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedTimeZone_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instInhabitedTimeZone_default___closed__1_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Std_Time_instInhabitedTimeZone_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instInhabitedTimeZone_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instInhabitedTimeZone_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedTimeZone_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedTimeZone_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedTimeZone: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 102, 102, 115, 101, 116, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [97, 98, 98, 114, 101, 118, 105, 97, 116, 105, 111, 110, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__16_value:
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
    m_data: [105, 115, 68, 83, 84, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__19_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__22_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone_repr___redArg___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimeZone_repr___redArg___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimeZone___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instReprTimeZone_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprTimeZone___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instReprTimeZone: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimeZone___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_UTC___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [85, 84, 67, 0],
    };
static mut l_Std_Time_TimeZone_UTC___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_UTC___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_UTC___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_UTC___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_UTC: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_GMT___closed__0_value: leanh::LeanStringObject<20> =
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
            71, 114, 101, 101, 110, 119, 105, 99, 104, 32, 77, 101, 97, 110, 32, 84, 105, 109, 101,
            0,
        ],
    };
static mut l_Std_Time_TimeZone_GMT___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_GMT___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_GMT___closed__1_value: leanh::LeanStringObject<4> =
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
        m_data: [71, 77, 84, 0],
    };
static mut l_Std_Time_TimeZone_GMT___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_GMT___closed__1_value) as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_GMT___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_GMT___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_GMT: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedTimeZone_default_spec__1(
    mut v_a_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ = lean_nat_to_int(v_a_184_);
    return v___x_185_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimeZone_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = leanh::lean_unsigned_to_nat(0);
    v___x_187_ = lean_nat_to_int(v___x_186_);
    return v___x_187_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimeZone_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_189_ = 0;
    v___x_190_ = l_Std_Time_instInhabitedTimeZone_default___closed__1;
    v___x_191_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimeZone_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimeZone_default___closed__0_once),
        _init_l_Std_Time_instInhabitedTimeZone_default___closed__0,
    );
    v___x_192_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_192_, 0, v___x_191_);
    leanh::lean_ctor_set(v___x_192_, 1, v___x_190_);
    leanh::lean_ctor_set(v___x_192_, 2, v___x_190_);
    leanh::lean_ctor_set_uint8(
        v___x_192_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_189_,
    );
    return v___x_192_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimeZone_default() -> *mut leanh::LeanObject {
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimeZone_default___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimeZone_default___closed__2_once),
        _init_l_Std_Time_instInhabitedTimeZone_default___closed__2,
    );
    return v___x_193_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedTimeZone_default_spec__0(
    mut v_a_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_195_ = lean_nat_to_int(v_a_194_);
    v___x_196_ = l_Rat_ofInt(v___x_195_);
    return v___x_196_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimeZone() -> *mut leanh::LeanObject {
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = l_Std_Time_instInhabitedTimeZone_default;
    return v___x_197_;
}
pub unsafe fn _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_211_ = leanh::lean_unsigned_to_nat(10);
    v___x_212_ = lean_nat_to_int(v___x_211_);
    return v___x_212_;
}
pub unsafe fn _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_219_ = leanh::lean_unsigned_to_nat(8);
    v___x_220_ = lean_nat_to_int(v___x_219_);
    return v___x_220_;
}
pub unsafe fn _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = leanh::lean_unsigned_to_nat(16);
    v___x_225_ = lean_nat_to_int(v___x_224_);
    return v___x_225_;
}
pub unsafe fn _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = leanh::lean_unsigned_to_nat(9);
    v___x_230_ = lean_nat_to_int(v___x_229_);
    return v___x_230_;
}
pub unsafe fn _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__0;
    v___x_233_ = lean_string_length(v___x_232_);
    return v___x_233_;
}
pub unsafe fn _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__20_once),
        _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__20,
    );
    v___x_235_ = lean_nat_to_int(v___x_234_);
    return v___x_235_;
}
pub unsafe fn l_Std_Time_instReprTimeZone_repr___redArg(
    mut v_x_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_244_: u8 = 0;
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: u8 = 0;
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_241_ = leanh::lean_ctor_get(v_x_240_, 0);
    leanh::lean_inc(v_offset_241_);
    v_name_242_ = leanh::lean_ctor_get(v_x_240_, 1);
    leanh::lean_inc_ref(v_name_242_);
    v_abbreviation_243_ = leanh::lean_ctor_get(v_x_240_, 2);
    leanh::lean_inc_ref(v_abbreviation_243_);
    v_isDST_244_ = leanh::lean_ctor_get_uint8(
        v_x_240_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    leanh::lean_dec_ref(v_x_240_);
    v___x_245_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__5;
    v___x_246_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__6;
    v___x_247_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__7,
    );
    v___x_248_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_241_);
    leanh::lean_dec(v_offset_241_);
    v___x_249_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_249_, 0, v___x_247_);
    leanh::lean_ctor_set(v___x_249_, 1, v___x_248_);
    v___x_250_ = 0;
    v___x_251_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_251_, 0, v___x_249_);
    leanh::lean_ctor_set_uint8(
        v___x_251_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_250_,
    );
    v___x_252_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_252_, 0, v___x_246_);
    leanh::lean_ctor_set(v___x_252_, 1, v___x_251_);
    v___x_253_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__9;
    v___x_254_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_254_, 0, v___x_252_);
    leanh::lean_ctor_set(v___x_254_, 1, v___x_253_);
    v___x_255_ = leanh::lean_box(1);
    v___x_256_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_256_, 0, v___x_254_);
    leanh::lean_ctor_set(v___x_256_, 1, v___x_255_);
    v___x_257_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__11;
    v___x_258_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_258_, 0, v___x_256_);
    leanh::lean_ctor_set(v___x_258_, 1, v___x_257_);
    v___x_259_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_259_, 0, v___x_258_);
    leanh::lean_ctor_set(v___x_259_, 1, v___x_245_);
    v___x_260_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__12_once),
        _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__12,
    );
    v___x_261_ = l_String_quote(v_name_242_);
    v___x_262_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_262_, 0, v___x_261_);
    v___x_263_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_263_, 0, v___x_260_);
    leanh::lean_ctor_set(v___x_263_, 1, v___x_262_);
    v___x_264_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_264_, 0, v___x_263_);
    leanh::lean_ctor_set_uint8(
        v___x_264_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_250_,
    );
    v___x_265_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_265_, 0, v___x_259_);
    leanh::lean_ctor_set(v___x_265_, 1, v___x_264_);
    v___x_266_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_266_, 0, v___x_265_);
    leanh::lean_ctor_set(v___x_266_, 1, v___x_253_);
    v___x_267_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_267_, 0, v___x_266_);
    leanh::lean_ctor_set(v___x_267_, 1, v___x_255_);
    v___x_268_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__14;
    v___x_269_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_269_, 0, v___x_267_);
    leanh::lean_ctor_set(v___x_269_, 1, v___x_268_);
    v___x_270_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_270_, 0, v___x_269_);
    leanh::lean_ctor_set(v___x_270_, 1, v___x_245_);
    v___x_271_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__15_once),
        _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__15,
    );
    v___x_272_ = l_String_quote(v_abbreviation_243_);
    v___x_273_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_273_, 0, v___x_272_);
    v___x_274_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_274_, 0, v___x_271_);
    leanh::lean_ctor_set(v___x_274_, 1, v___x_273_);
    v___x_275_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_275_, 0, v___x_274_);
    leanh::lean_ctor_set_uint8(
        v___x_275_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_250_,
    );
    v___x_276_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_276_, 0, v___x_270_);
    leanh::lean_ctor_set(v___x_276_, 1, v___x_275_);
    v___x_277_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_277_, 0, v___x_276_);
    leanh::lean_ctor_set(v___x_277_, 1, v___x_253_);
    v___x_278_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_278_, 0, v___x_277_);
    leanh::lean_ctor_set(v___x_278_, 1, v___x_255_);
    v___x_279_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__17;
    v___x_280_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_280_, 0, v___x_278_);
    leanh::lean_ctor_set(v___x_280_, 1, v___x_279_);
    v___x_281_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_281_, 0, v___x_280_);
    leanh::lean_ctor_set(v___x_281_, 1, v___x_245_);
    v___x_282_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__18_once),
        _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__18,
    );
    v___x_283_ = l_Bool_repr___redArg(v_isDST_244_);
    v___x_284_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_284_, 0, v___x_282_);
    leanh::lean_ctor_set(v___x_284_, 1, v___x_283_);
    v___x_285_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_285_, 0, v___x_284_);
    leanh::lean_ctor_set_uint8(
        v___x_285_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_250_,
    );
    v___x_286_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_286_, 0, v___x_281_);
    leanh::lean_ctor_set(v___x_286_, 1, v___x_285_);
    v___x_287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimeZone_repr___redArg___closed__21_once),
        _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__21,
    );
    v___x_288_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__22;
    v___x_289_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_289_, 0, v___x_288_);
    leanh::lean_ctor_set(v___x_289_, 1, v___x_286_);
    v___x_290_ = l_Std_Time_instReprTimeZone_repr___redArg___closed__23;
    v___x_291_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_291_, 0, v___x_289_);
    leanh::lean_ctor_set(v___x_291_, 1, v___x_290_);
    v___x_292_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_292_, 0, v___x_287_);
    leanh::lean_ctor_set(v___x_292_, 1, v___x_291_);
    v___x_293_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_293_, 0, v___x_292_);
    leanh::lean_ctor_set_uint8(
        v___x_293_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_250_,
    );
    return v___x_293_;
}
pub unsafe fn l_Std_Time_instReprTimeZone_repr(
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_prec_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_296_ = l_Std_Time_instReprTimeZone_repr___redArg(v_x_294_);
    return v___x_296_;
}
pub unsafe fn l_Std_Time_instReprTimeZone_repr___boxed(
    mut v_x_297_: *mut leanh::LeanObject,
    mut v_prec_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_299_ = l_Std_Time_instReprTimeZone_repr(v_x_297_, v_prec_298_);
    leanh::lean_dec(v_prec_298_);
    return v_res_299_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimeZone_decEq(
    mut v_x_302_: *mut leanh::LeanObject,
    mut v_x_303_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_offset_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_307_: u8 = 0;
    let mut v_offset_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_311_: u8 = 0;
    let mut v___x_312_: u8 = 0;
    v_offset_304_ = leanh::lean_ctor_get(v_x_302_, 0);
    v_name_305_ = leanh::lean_ctor_get(v_x_302_, 1);
    v_abbreviation_306_ = leanh::lean_ctor_get(v_x_302_, 2);
    v_isDST_307_ = leanh::lean_ctor_get_uint8(
        v_x_302_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_offset_308_ = leanh::lean_ctor_get(v_x_303_, 0);
    v_name_309_ = leanh::lean_ctor_get(v_x_303_, 1);
    v_abbreviation_310_ = leanh::lean_ctor_get(v_x_303_, 2);
    v_isDST_311_ = leanh::lean_ctor_get_uint8(
        v_x_303_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_312_ = lean_int_dec_eq(v_offset_304_, v_offset_308_);
    if v___x_312_ == 0 {
        return v___x_312_;
    } else {
        let mut v___x_313_: u8 = 0;
        v___x_313_ = lean_string_dec_eq(v_name_305_, v_name_309_);
        if v___x_313_ == 0 {
            return v___x_313_;
        } else {
            let mut v___x_314_: u8 = 0;
            v___x_314_ = lean_string_dec_eq(v_abbreviation_306_, v_abbreviation_310_);
            if v___x_314_ == 0 {
                return v___x_314_;
            } else {
                if v_isDST_307_ == 0 {
                    if v_isDST_311_ == 0 {
                        return v___x_314_;
                    } else {
                        return v_isDST_307_;
                    }
                } else {
                    return v_isDST_311_;
                }
            }
        }
    }
}
pub unsafe fn l_Std_Time_instDecidableEqTimeZone_decEq___boxed(
    mut v_x_315_: *mut leanh::LeanObject,
    mut v_x_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_317_: u8 = 0;
    let mut v_r_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_315_, v_x_316_);
    leanh::lean_dec_ref(v_x_316_);
    leanh::lean_dec_ref(v_x_315_);
    v_r_318_ = leanh::lean_box((v_res_317_) as usize);
    return v_r_318_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimeZone(
    mut v_x_319_: *mut leanh::LeanObject,
    mut v_x_320_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_321_: u8 = 0;
    v___x_321_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_319_, v_x_320_);
    return v___x_321_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimeZone___boxed(
    mut v_x_322_: *mut leanh::LeanObject,
    mut v_x_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_324_: u8 = 0;
    let mut v_r_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_324_ = l_Std_Time_instDecidableEqTimeZone(v_x_322_, v_x_323_);
    leanh::lean_dec_ref(v_x_323_);
    leanh::lean_dec_ref(v_x_322_);
    v_r_325_ = leanh::lean_box((v_res_324_) as usize);
    return v_r_325_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_UTC___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_327_: u8 = 0;
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = 0;
    v___x_328_ = l_Std_Time_TimeZone_UTC___closed__0;
    v___x_329_ = l_Std_Time_TimeZone_Offset_zero;
    v___x_330_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_330_, 0, v___x_329_);
    leanh::lean_ctor_set(v___x_330_, 1, v___x_328_);
    leanh::lean_ctor_set(v___x_330_, 2, v___x_328_);
    leanh::lean_ctor_set_uint8(
        v___x_330_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_327_,
    );
    return v___x_330_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_UTC() -> *mut leanh::LeanObject {
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_331_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_UTC___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_UTC___closed__1_once),
        _init_l_Std_Time_TimeZone_UTC___closed__1,
    );
    return v___x_331_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_GMT___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_334_: u8 = 0;
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = 0;
    v___x_335_ = l_Std_Time_TimeZone_GMT___closed__1;
    v___x_336_ = l_Std_Time_TimeZone_GMT___closed__0;
    v___x_337_ = l_Std_Time_TimeZone_Offset_zero;
    v___x_338_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_338_, 0, v___x_337_);
    leanh::lean_ctor_set(v___x_338_, 1, v___x_336_);
    leanh::lean_ctor_set(v___x_338_, 2, v___x_335_);
    leanh::lean_ctor_set_uint8(
        v___x_338_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_334_,
    );
    return v___x_338_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_GMT() -> *mut leanh::LeanObject {
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_GMT___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_GMT___closed__2_once),
        _init_l_Std_Time_TimeZone_GMT___closed__2,
    );
    return v___x_339_;
}
pub unsafe fn l_Std_Time_TimeZone_ofHours(
    mut v_name_340_: *mut leanh::LeanObject,
    mut v_abbreviation_341_: *mut leanh::LeanObject,
    mut v_n_342_: *mut leanh::LeanObject,
    mut v_isDST_343_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_342_);
    v___x_345_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_345_, 0, v___x_344_);
    leanh::lean_ctor_set(v___x_345_, 1, v_name_340_);
    leanh::lean_ctor_set(v___x_345_, 2, v_abbreviation_341_);
    leanh::lean_ctor_set_uint8(
        v___x_345_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_isDST_343_,
    );
    return v___x_345_;
}
pub unsafe fn l_Std_Time_TimeZone_ofHours___boxed(
    mut v_name_346_: *mut leanh::LeanObject,
    mut v_abbreviation_347_: *mut leanh::LeanObject,
    mut v_n_348_: *mut leanh::LeanObject,
    mut v_isDST_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isDST_boxed_350_: u8 = 0;
    let mut v_res_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isDST_boxed_350_ = (leanh::lean_unbox(v_isDST_349_) as u8);
    v_res_351_ = l_Std_Time_TimeZone_ofHours(
        v_name_346_,
        v_abbreviation_347_,
        v_n_348_,
        v_isDST_boxed_350_,
    );
    leanh::lean_dec(v_n_348_);
    return v_res_351_;
}
pub unsafe fn l_Std_Time_TimeZone_ofSeconds(
    mut v_name_352_: *mut leanh::LeanObject,
    mut v_abbreviation_353_: *mut leanh::LeanObject,
    mut v_n_354_: *mut leanh::LeanObject,
    mut v_isDST_355_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_356_, 0, v_n_354_);
    leanh::lean_ctor_set(v___x_356_, 1, v_name_352_);
    leanh::lean_ctor_set(v___x_356_, 2, v_abbreviation_353_);
    leanh::lean_ctor_set_uint8(
        v___x_356_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_isDST_355_,
    );
    return v___x_356_;
}
pub unsafe fn l_Std_Time_TimeZone_ofSeconds___boxed(
    mut v_name_357_: *mut leanh::LeanObject,
    mut v_abbreviation_358_: *mut leanh::LeanObject,
    mut v_n_359_: *mut leanh::LeanObject,
    mut v_isDST_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isDST_boxed_361_: u8 = 0;
    let mut v_res_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isDST_boxed_361_ = (leanh::lean_unbox(v_isDST_360_) as u8);
    v_res_362_ = l_Std_Time_TimeZone_ofSeconds(
        v_name_357_,
        v_abbreviation_358_,
        v_n_359_,
        v_isDST_boxed_361_,
    );
    return v_res_362_;
}
pub unsafe fn l_Std_Time_TimeZone_toSeconds(
    mut v_tz_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_364_ = leanh::lean_ctor_get(v_tz_363_, 0);
    leanh::lean_inc(v_offset_364_);
    return v_offset_364_;
}
pub unsafe fn l_Std_Time_TimeZone_toSeconds___boxed(
    mut v_tz_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Std_Time_TimeZone_toSeconds(v_tz_365_);
    leanh::lean_dec_ref(v_tz_365_);
    return v_res_366_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_TimeZone(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedTimeZone_default = _init_l_Std_Time_instInhabitedTimeZone_default();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedTimeZone_default);
    l_Std_Time_instInhabitedTimeZone = _init_l_Std_Time_instInhabitedTimeZone();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedTimeZone);
    l_Std_Time_TimeZone_UTC = _init_l_Std_Time_TimeZone_UTC();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_UTC);
    l_Std_Time_TimeZone_GMT = _init_l_Std_Time_TimeZone_GMT();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_GMT);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_TimeZone(
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
pub unsafe fn initialize_Std_Time_Zoned_TimeZone(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_TimeZone(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_TimeZone(builtin);
}