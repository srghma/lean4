// Lean compiler output
// Module: Std.Time.Time.PlainTime
// Imports: Std.Time.Time.Basic
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::{l_compareLex___boxed, l_compareOn___boxed};
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Time::Basic::{
    initialize_Std_Time_Time_Basic, runtime_initialize_Std_Time_Time_Basic,
};
use crate::r#gen::Std::Time::Time::Unit::Hour::{
    l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed, l_Std_Time_Hour_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::Time::Unit::Minute::{
    l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed, l_Std_Time_Minute_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::Time::Unit::Nanosecond::{
    l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed,
    l_Std_Time_Nanosecond_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::Time::Unit::Second::{
    l_Std_Time_Second_instOfNatOrdinal, l_Std_Time_Second_instOrdOrdinal___aux__1___boxed,
};
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::ffi::{
    lean_int_div, lean_int_ediv, lean_int_emod,
};
use crate::ffi::lean_string_length;
use crate::ffi::lean_nat_mod;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 117, 114, 0],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 105, 110, 117, 116, 101, 0],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 101, 99, 111, 110, 100, 0],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [110, 97, 110, 111, 115, 101, 99, 111, 110, 100, 0],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__16_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__21_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__22_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instReprPlainTime_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprPlainTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprPlainTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instInhabitedPlainTime___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainTime___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainTime: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instOrdPlainTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__7_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__8_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__9_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Second_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_instOrdPlainTime___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__10_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__11_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__12_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__13_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__14_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instOrdPlainTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_PlainTime_midnight___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_midnight___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_PlainTime_midnight: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toMilliseconds___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toMilliseconds___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toMilliseconds___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toNanoseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toNanoseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toNanoseconds___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toNanoseconds___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toNanoseconds___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toNanoseconds___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toSeconds___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_toSeconds___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_ofNanoseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_ofNanoseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainTime_instHAddOffset___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_PlainTime_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_PlainTime_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHAddOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHSubOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHAddOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHSubOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHAddOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_instHSubOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprPlainTime_repr_spec__0(
    mut v_a_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = lean_nat_to_int(v_a_635_);
    return v___x_636_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_651_ = lean_nat_to_int(v___x_650_);
    return v___x_651_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_659_ = lean_nat_to_int(v___x_658_);
    return v___x_659_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_667_ = lean_nat_to_int(v___x_666_);
    return v___x_667_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_669_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__0;
    v___x_670_ = lean_string_length(v___x_669_);
    return v___x_670_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__19_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__19,
    );
    v___x_672_ = lean_nat_to_int(v___x_671_);
    return v___x_672_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_678_ = lean_nat_to_int(v___x_677_);
    return v___x_678_;
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr___redArg(
    mut v_x_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_680_ = crate::leanh::lean_ctor_get(v_x_679_, 0);
                v_minute_681_ = crate::leanh::lean_ctor_get(v_x_679_, 1);
                v_second_682_ = crate::leanh::lean_ctor_get(v_x_679_, 2);
                v_nanosecond_683_ = crate::leanh::lean_ctor_get(v_x_679_, 3);
                v___x_684_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__5;
                v___x_685_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__6;
                v___x_686_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__7,
                );
                v___x_687_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_688_ = l_Std_Time_Hour_instReprOrdinal___lam__0(v_hour_680_, v___x_687_);
                v___x_689_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_686_);
                crate::leanh::lean_ctor_set(v___x_689_, 1, v___x_688_);
                v___x_690_ = 0;
                v___x_691_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_691_, 0, v___x_689_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_691_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_692_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_685_);
                crate::leanh::lean_ctor_set(v___x_692_, 1, v___x_691_);
                v___x_693_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__9;
                v___x_694_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_694_, 0, v___x_692_);
                crate::leanh::lean_ctor_set(v___x_694_, 1, v___x_693_);
                v___x_695_ = crate::leanh::lean_box(1);
                v___x_696_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_696_, 0, v___x_694_);
                crate::leanh::lean_ctor_set(v___x_696_, 1, v___x_695_);
                v___x_697_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__11;
                v___x_698_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_698_, 0, v___x_696_);
                crate::leanh::lean_ctor_set(v___x_698_, 1, v___x_697_);
                v___x_699_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_699_, 0, v___x_698_);
                crate::leanh::lean_ctor_set(v___x_699_, 1, v___x_684_);
                v___x_700_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__12_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__12,
                );
                v___x_701_ = l_Std_Time_Minute_instReprOrdinal___lam__0(v_minute_681_, v___x_687_);
                v___x_702_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_702_, 0, v___x_700_);
                crate::leanh::lean_ctor_set(v___x_702_, 1, v___x_701_);
                v___x_703_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_703_, 0, v___x_702_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_703_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_704_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_704_, 0, v___x_699_);
                crate::leanh::lean_ctor_set(v___x_704_, 1, v___x_703_);
                v___x_705_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_705_, 0, v___x_704_);
                crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_693_);
                v___x_706_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_706_, 0, v___x_705_);
                crate::leanh::lean_ctor_set(v___x_706_, 1, v___x_695_);
                v___x_707_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__14;
                v___x_708_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_708_, 0, v___x_706_);
                crate::leanh::lean_ctor_set(v___x_708_, 1, v___x_707_);
                v___x_709_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_709_, 0, v___x_708_);
                crate::leanh::lean_ctor_set(v___x_709_, 1, v___x_684_);
                v___x_732_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__23
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
                );
                v___x_733_ = lean_int_dec_lt(v_second_682_, v___x_732_);
                if v___x_733_ == 0 {
                    v___x_734_ = l_Int_repr(v_second_682_);
                    v___x_735_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_735_, 0, v___x_734_);
                    v___y_711_ = v___x_735_;
                    state = 1;
                    continue;
                } else {
                    v___x_736_ = l_Int_repr(v_second_682_);
                    v___x_737_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_737_, 0, v___x_736_);
                    v___x_738_ = l_Repr_addAppParen(v___x_737_, v___x_687_);
                    v___y_711_ = v___x_738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_712_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_712_, 0, v___x_700_);
                crate::leanh::lean_ctor_set(v___x_712_, 1, v___y_711_);
                v___x_713_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_712_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_713_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_714_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_714_, 0, v___x_709_);
                crate::leanh::lean_ctor_set(v___x_714_, 1, v___x_713_);
                v___x_715_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_714_);
                crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_693_);
                v___x_716_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_716_, 0, v___x_715_);
                crate::leanh::lean_ctor_set(v___x_716_, 1, v___x_695_);
                v___x_717_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__16;
                v___x_718_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_718_, 0, v___x_716_);
                crate::leanh::lean_ctor_set(v___x_718_, 1, v___x_717_);
                v___x_719_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_719_, 0, v___x_718_);
                crate::leanh::lean_ctor_set(v___x_719_, 1, v___x_684_);
                v___x_720_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__17_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__17,
                );
                v___x_721_ =
                    l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanosecond_683_, v___x_687_);
                v___x_722_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_722_, 0, v___x_720_);
                crate::leanh::lean_ctor_set(v___x_722_, 1, v___x_721_);
                v___x_723_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_722_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_724_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_724_, 0, v___x_719_);
                crate::leanh::lean_ctor_set(v___x_724_, 1, v___x_723_);
                v___x_725_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__20_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__20,
                );
                v___x_726_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__21;
                v___x_727_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_727_, 0, v___x_726_);
                crate::leanh::lean_ctor_set(v___x_727_, 1, v___x_724_);
                v___x_728_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__22;
                v___x_729_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_729_, 0, v___x_727_);
                crate::leanh::lean_ctor_set(v___x_729_, 1, v___x_728_);
                v___x_730_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_730_, 0, v___x_725_);
                crate::leanh::lean_ctor_set(v___x_730_, 1, v___x_729_);
                v___x_731_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_731_, 0, v___x_730_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_731_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                return v___x_731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr___redArg___boxed(
    mut v_x_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ = l_Std_Time_instReprPlainTime_repr___redArg(v_x_739_);
    crate::leanh::lean_dec_ref(v_x_739_);
    return v_res_740_;
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr(
    mut v_x_741_: *mut crate::leanh::LeanObject,
    mut v_prec_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = l_Std_Time_instReprPlainTime_repr___redArg(v_x_741_);
    return v___x_743_;
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr___boxed(
    mut v_x_744_: *mut crate::leanh::LeanObject,
    mut v_prec_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Std_Time_instReprPlainTime_repr(v_x_744_, v_prec_745_);
    crate::leanh::lean_dec(v_prec_745_);
    crate::leanh::lean_dec_ref(v_x_744_);
    return v_res_746_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime_decEq(
    mut v_x_749_: *mut crate::leanh::LeanObject,
    mut v_x_750_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_hour_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u8 = 0;
    v_hour_751_ = crate::leanh::lean_ctor_get(v_x_749_, 0);
    v_minute_752_ = crate::leanh::lean_ctor_get(v_x_749_, 1);
    v_second_753_ = crate::leanh::lean_ctor_get(v_x_749_, 2);
    v_nanosecond_754_ = crate::leanh::lean_ctor_get(v_x_749_, 3);
    v_hour_755_ = crate::leanh::lean_ctor_get(v_x_750_, 0);
    v_minute_756_ = crate::leanh::lean_ctor_get(v_x_750_, 1);
    v_second_757_ = crate::leanh::lean_ctor_get(v_x_750_, 2);
    v_nanosecond_758_ = crate::leanh::lean_ctor_get(v_x_750_, 3);
    v___x_759_ = lean_int_dec_eq(v_hour_751_, v_hour_755_);
    if v___x_759_ == 0 {
        return v___x_759_;
    } else {
        let mut v___x_760_: u8 = 0;
        v___x_760_ = lean_int_dec_eq(v_minute_752_, v_minute_756_);
        if v___x_760_ == 0 {
            return v___x_760_;
        } else {
            let mut v___x_761_: u8 = 0;
            v___x_761_ = lean_int_dec_eq(v_second_753_, v_second_757_);
            if v___x_761_ == 0 {
                return v___x_761_;
            } else {
                let mut v___x_762_: u8 = 0;
                v___x_762_ = lean_int_dec_eq(v_nanosecond_754_, v_nanosecond_758_);
                return v___x_762_;
            }
        }
    }
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime_decEq___boxed(
    mut v_x_763_: *mut crate::leanh::LeanObject,
    mut v_x_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_763_, v_x_764_);
    crate::leanh::lean_dec_ref(v_x_764_);
    crate::leanh::lean_dec_ref(v_x_763_);
    v_r_766_ = crate::leanh::lean_box((v_res_765_) as usize);
    return v_r_766_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime(
    mut v_x_767_: *mut crate::leanh::LeanObject,
    mut v_x_768_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_769_: u8 = 0;
    v___x_769_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_767_, v_x_768_);
    return v___x_769_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime___boxed(
    mut v_x_770_: *mut crate::leanh::LeanObject,
    mut v_x_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Std_Time_instDecidableEqPlainTime(v_x_770_, v_x_771_);
    crate::leanh::lean_dec_ref(v_x_771_);
    crate::leanh::lean_dec_ref(v_x_770_);
    v_r_773_ = crate::leanh::lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_775_ = lean_nat_to_int(v___x_774_);
    return v___x_775_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__0,
    );
    v___x_777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_778_ = lean_int_add(v___x_777_, v___x_776_);
    return v___x_778_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__1,
    );
    v___x_781_ = lean_int_sub(v___x_780_, v___x_779_);
    return v___x_781_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_782_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_783_ = lean_nat_to_int(v___x_782_);
    return v___x_783_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_785_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__2_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__2,
    );
    v_range_786_ = lean_int_add(v___x_785_, v___x_784_);
    return v_range_786_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_788_ = lean_int_sub(v___x_787_, v___x_787_);
    return v___x_788_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v_range_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_789_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__4,
    );
    v___x_790_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_791_ = lean_int_emod(v___x_790_, v_range_789_);
    return v___x_791_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v_range_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__4,
    );
    v___x_793_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__6,
    );
    v___x_794_ = lean_int_add(v___x_793_, v_range_792_);
    return v___x_794_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v_range_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_795_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__4,
    );
    v___x_796_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__7_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__7,
    );
    v___x_797_ = lean_int_emod(v___x_796_, v_range_795_);
    return v___x_797_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_799_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__8_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__8,
    );
    v___x_800_ = lean_int_add(v___x_799_, v___x_798_);
    return v___x_800_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_801_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_802_ = lean_nat_to_int(v___x_801_);
    return v___x_802_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_803_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__10_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__10,
    );
    v___x_804_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_805_ = lean_int_add(v___x_804_, v___x_803_);
    return v___x_805_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_807_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__11,
    );
    v___x_808_ = lean_int_sub(v___x_807_, v___x_806_);
    return v___x_808_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__12_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__12,
    );
    v_range_811_ = lean_int_add(v___x_810_, v___x_809_);
    return v_range_811_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v_range_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_812_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__13,
    );
    v___x_813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_814_ = lean_int_emod(v___x_813_, v_range_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v_range_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__13,
    );
    v___x_816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__14,
    );
    v___x_817_ = lean_int_add(v___x_816_, v_range_815_);
    return v___x_817_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__16() -> *mut crate::leanh::LeanObject
{
    let mut v_range_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_818_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__13,
    );
    v___x_819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__15_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__15,
    );
    v___x_820_ = lean_int_emod(v___x_819_, v_range_818_);
    return v___x_820_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__16_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__16,
    );
    v___x_823_ = lean_int_add(v___x_822_, v___x_821_);
    return v___x_823_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__18() -> *mut crate::leanh::LeanObject
{
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_825_ = 1;
    v___x_826_ = l_Std_Time_Second_instOfNatOrdinal(v___x_825_, v___x_824_);
    return v___x_826_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__19() -> *mut crate::leanh::LeanObject
{
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__18,
    );
    v___x_829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__17,
    );
    v___x_830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__9,
    );
    v___x_831_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_830_);
    crate::leanh::lean_ctor_set(v___x_831_, 1, v___x_829_);
    crate::leanh::lean_ctor_set(v___x_831_, 2, v___x_828_);
    crate::leanh::lean_ctor_set(v___x_831_, 3, v___x_827_);
    return v___x_831_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__19_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__19,
    );
    return v___x_832_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__0(
    mut v_x_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_834_ = crate::leanh::lean_ctor_get(v_x_833_, 0);
    crate::leanh::lean_inc(v_hour_834_);
    return v_hour_834_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__0___boxed(
    mut v_x_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Std_Time_instOrdPlainTime___lam__0(v_x_835_);
    crate::leanh::lean_dec_ref(v_x_835_);
    return v_res_836_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__1(
    mut v_x_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minute_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_minute_838_ = crate::leanh::lean_ctor_get(v_x_837_, 1);
    crate::leanh::lean_inc(v_minute_838_);
    return v_minute_838_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__1___boxed(
    mut v_x_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Std_Time_instOrdPlainTime___lam__1(v_x_839_);
    crate::leanh::lean_dec_ref(v_x_839_);
    return v_res_840_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__2(
    mut v_x_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_842_ = crate::leanh::lean_ctor_get(v_x_841_, 2);
    crate::leanh::lean_inc(v_second_842_);
    return v_second_842_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__2___boxed(
    mut v_x_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Std_Time_instOrdPlainTime___lam__2(v_x_843_);
    crate::leanh::lean_dec_ref(v_x_843_);
    return v_res_844_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__3(
    mut v_x_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nanosecond_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nanosecond_846_ = crate::leanh::lean_ctor_get(v_x_845_, 3);
    crate::leanh::lean_inc(v_nanosecond_846_);
    return v_nanosecond_846_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__3___boxed(
    mut v_x_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_848_ = l_Std_Time_instOrdPlainTime___lam__3(v_x_847_);
    crate::leanh::lean_dec_ref(v_x_847_);
    return v_res_848_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_882_ = lean_nat_to_int(v___x_881_);
    return v___x_882_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__0_once),
        _init_l_Std_Time_PlainTime_midnight___closed__0,
    );
    v___x_884_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_885_ = lean_int_add(v___x_884_, v___x_883_);
    return v___x_885_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_887_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__1_once),
        _init_l_Std_Time_PlainTime_midnight___closed__1,
    );
    v___x_888_ = lean_int_sub(v___x_887_, v___x_886_);
    return v___x_888_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_890_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__2_once),
        _init_l_Std_Time_PlainTime_midnight___closed__2,
    );
    v_range_891_ = lean_int_add(v___x_890_, v___x_889_);
    return v_range_891_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3_once),
        _init_l_Std_Time_PlainTime_midnight___closed__3,
    );
    v___x_893_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_894_ = lean_int_emod(v___x_893_, v_range_892_);
    return v___x_894_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v_range_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_895_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3_once),
        _init_l_Std_Time_PlainTime_midnight___closed__3,
    );
    v___x_896_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__4_once),
        _init_l_Std_Time_PlainTime_midnight___closed__4,
    );
    v___x_897_ = lean_int_add(v___x_896_, v_range_895_);
    return v___x_897_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v_range_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_898_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3_once),
        _init_l_Std_Time_PlainTime_midnight___closed__3,
    );
    v___x_899_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__5_once),
        _init_l_Std_Time_PlainTime_midnight___closed__5,
    );
    v___x_900_ = lean_int_emod(v___x_899_, v_range_898_);
    return v___x_900_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_902_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__6_once),
        _init_l_Std_Time_PlainTime_midnight___closed__6,
    );
    v___x_903_ = lean_int_add(v___x_902_, v___x_901_);
    return v___x_903_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_905_ = lean_nat_to_int(v___x_904_);
    return v___x_905_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__8_once),
        _init_l_Std_Time_PlainTime_midnight___closed__8,
    );
    v___x_907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_908_ = lean_int_add(v___x_907_, v___x_906_);
    return v___x_908_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__9_once),
        _init_l_Std_Time_PlainTime_midnight___closed__9,
    );
    v___x_911_ = lean_int_sub(v___x_910_, v___x_909_);
    return v___x_911_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__10_once),
        _init_l_Std_Time_PlainTime_midnight___closed__10,
    );
    v_range_914_ = lean_int_add(v___x_913_, v___x_912_);
    return v_range_914_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v_range_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_915_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11_once),
        _init_l_Std_Time_PlainTime_midnight___closed__11,
    );
    v___x_916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_917_ = lean_int_emod(v___x_916_, v_range_915_);
    return v___x_917_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v_range_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_918_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11_once),
        _init_l_Std_Time_PlainTime_midnight___closed__11,
    );
    v___x_919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__12_once),
        _init_l_Std_Time_PlainTime_midnight___closed__12,
    );
    v___x_920_ = lean_int_add(v___x_919_, v_range_918_);
    return v___x_920_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v_range_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_921_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11_once),
        _init_l_Std_Time_PlainTime_midnight___closed__11,
    );
    v___x_922_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__13_once),
        _init_l_Std_Time_PlainTime_midnight___closed__13,
    );
    v___x_923_ = lean_int_emod(v___x_922_, v_range_921_);
    return v___x_923_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_925_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__14_once),
        _init_l_Std_Time_PlainTime_midnight___closed__14,
    );
    v___x_926_ = lean_int_add(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_928_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_929_ = lean_nat_mod(v___x_928_, v___x_927_);
    return v___x_929_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_930_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16_once),
        _init_l_Std_Time_PlainTime_midnight___closed__16,
    );
    v___x_931_ = lean_nat_to_int(v___x_930_);
    return v___x_931_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__17_once),
        _init_l_Std_Time_PlainTime_midnight___closed__17,
    );
    v___x_933_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__18,
    );
    v___x_934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__15_once),
        _init_l_Std_Time_PlainTime_midnight___closed__15,
    );
    v___x_935_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__7_once),
        _init_l_Std_Time_PlainTime_midnight___closed__7,
    );
    v___x_936_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
    crate::leanh::lean_ctor_set(v___x_936_, 1, v___x_934_);
    crate::leanh::lean_ctor_set(v___x_936_, 2, v___x_933_);
    crate::leanh::lean_ctor_set(v___x_936_, 3, v___x_932_);
    return v___x_936_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight() -> *mut crate::leanh::LeanObject {
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__18_once),
        _init_l_Std_Time_PlainTime_midnight___closed__18,
    );
    return v___x_937_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHourMinuteSecondsNano(
    mut v_hour_938_: *mut crate::leanh::LeanObject,
    mut v_minute_939_: *mut crate::leanh::LeanObject,
    mut v_second_940_: *mut crate::leanh::LeanObject,
    mut v_nano_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_942_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_942_, 0, v_hour_938_);
    crate::leanh::lean_ctor_set(v___x_942_, 1, v_minute_939_);
    crate::leanh::lean_ctor_set(v___x_942_, 2, v_second_940_);
    crate::leanh::lean_ctor_set(v___x_942_, 3, v_nano_941_);
    return v___x_942_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16_once),
        _init_l_Std_Time_PlainTime_midnight___closed__16,
    );
    v___x_944_ = lean_nat_to_int(v___x_943_);
    return v___x_944_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHourMinuteSeconds(
    mut v_hour_945_: *mut crate::leanh::LeanObject,
    mut v_minute_946_: *mut crate::leanh::LeanObject,
    mut v_second_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once),
        _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0,
    );
    v___x_949_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_949_, 0, v_hour_945_);
    crate::leanh::lean_ctor_set(v___x_949_, 1, v_minute_946_);
    crate::leanh::lean_ctor_set(v___x_949_, 2, v_second_947_);
    crate::leanh::lean_ctor_set(v___x_949_, 3, v___x_948_);
    return v___x_949_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(
    mut v_a_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = l_Rat_ofInt(v_a_950_);
    return v___x_951_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = crate::leanh::lean_unsigned_to_nat(3600000);
    v___x_953_ = lean_nat_to_int(v___x_952_);
    return v___x_953_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_954_ = crate::leanh::lean_unsigned_to_nat(60000);
    v___x_955_ = lean_nat_to_int(v___x_954_);
    return v___x_955_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_957_ = lean_nat_to_int(v___x_956_);
    return v___x_957_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_959_ = lean_nat_to_int(v___x_958_);
    return v___x_959_;
}
pub unsafe fn l_Std_Time_PlainTime_toMilliseconds(
    mut v_time_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_961_ = crate::leanh::lean_ctor_get(v_time_960_, 0);
    v_minute_962_ = crate::leanh::lean_ctor_get(v_time_960_, 1);
    v_second_963_ = crate::leanh::lean_ctor_get(v_time_960_, 2);
    v_nanosecond_964_ = crate::leanh::lean_ctor_get(v_time_960_, 3);
    v___x_965_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__0,
    );
    v___x_966_ = lean_int_mul(v_hour_961_, v___x_965_);
    v___x_967_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__1,
    );
    v___x_968_ = lean_int_mul(v_minute_962_, v___x_967_);
    v___x_969_ = lean_int_add(v___x_966_, v___x_968_);
    crate::leanh::lean_dec(v___x_968_);
    crate::leanh::lean_dec(v___x_966_);
    v___x_970_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__2,
    );
    v___x_971_ = lean_int_mul(v_second_963_, v___x_970_);
    v___x_972_ = lean_int_add(v___x_969_, v___x_971_);
    crate::leanh::lean_dec(v___x_971_);
    crate::leanh::lean_dec(v___x_969_);
    v___x_973_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_974_ = lean_int_div(v_nanosecond_964_, v___x_973_);
    v___x_975_ = lean_int_add(v___x_972_, v___x_974_);
    crate::leanh::lean_dec(v___x_974_);
    crate::leanh::lean_dec(v___x_972_);
    return v___x_975_;
}
pub unsafe fn l_Std_Time_PlainTime_toMilliseconds___boxed(
    mut v_time_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_977_ = l_Std_Time_PlainTime_toMilliseconds(v_time_976_);
    crate::leanh::lean_dec_ref(v_time_976_);
    return v_res_977_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(
    mut v_a_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ = lean_nat_to_int(v_a_978_);
    v___x_980_ = l_Rat_ofInt(v___x_979_);
    return v___x_980_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toNanoseconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_981_ = crate::leanh::lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_982_ = lean_nat_to_int(v___x_981_);
    return v___x_982_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toNanoseconds___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = crate::leanh::lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_984_ = lean_nat_to_int(v___x_983_);
    return v___x_984_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toNanoseconds___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_986_ = lean_nat_to_int(v___x_985_);
    return v___x_986_;
}
pub unsafe fn l_Std_Time_PlainTime_toNanoseconds(
    mut v_time_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_988_ = crate::leanh::lean_ctor_get(v_time_987_, 0);
    v_minute_989_ = crate::leanh::lean_ctor_get(v_time_987_, 1);
    v_second_990_ = crate::leanh::lean_ctor_get(v_time_987_, 2);
    v_nanosecond_991_ = crate::leanh::lean_ctor_get(v_time_987_, 3);
    v___x_992_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_993_ = lean_int_mul(v_hour_988_, v___x_992_);
    v___x_994_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_995_ = lean_int_mul(v_minute_989_, v___x_994_);
    v___x_996_ = lean_int_add(v___x_993_, v___x_995_);
    crate::leanh::lean_dec(v___x_995_);
    crate::leanh::lean_dec(v___x_993_);
    v___x_997_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_998_ = lean_int_mul(v_second_990_, v___x_997_);
    v___x_999_ = lean_int_add(v___x_996_, v___x_998_);
    crate::leanh::lean_dec(v___x_998_);
    crate::leanh::lean_dec(v___x_996_);
    v___x_1000_ = lean_int_add(v___x_999_, v_nanosecond_991_);
    crate::leanh::lean_dec(v___x_999_);
    return v___x_1000_;
}
pub unsafe fn l_Std_Time_PlainTime_toNanoseconds___boxed(
    mut v_time_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1001_);
    crate::leanh::lean_dec_ref(v_time_1001_);
    return v_res_1002_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toSeconds___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_1004_ = lean_nat_to_int(v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toSeconds___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_1006_ = lean_nat_to_int(v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Std_Time_PlainTime_toSeconds(
    mut v_time_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_1008_ = crate::leanh::lean_ctor_get(v_time_1007_, 0);
    v_minute_1009_ = crate::leanh::lean_ctor_get(v_time_1007_, 1);
    v_second_1010_ = crate::leanh::lean_ctor_get(v_time_1007_, 2);
    v___x_1011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__0,
    );
    v___x_1012_ = lean_int_mul(v_hour_1008_, v___x_1011_);
    v___x_1013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__1,
    );
    v___x_1014_ = lean_int_mul(v_minute_1009_, v___x_1013_);
    v___x_1015_ = lean_int_add(v___x_1012_, v___x_1014_);
    crate::leanh::lean_dec(v___x_1014_);
    crate::leanh::lean_dec(v___x_1012_);
    v___x_1016_ = lean_int_add(v___x_1015_, v_second_1010_);
    crate::leanh::lean_dec(v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Time_PlainTime_toSeconds___boxed(
    mut v_time_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_Time_PlainTime_toSeconds(v_time_1017_);
    crate::leanh::lean_dec_ref(v_time_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Std_Time_PlainTime_toMinutes(
    mut v_time_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_1020_ = crate::leanh::lean_ctor_get(v_time_1019_, 0);
    v_minute_1021_ = crate::leanh::lean_ctor_get(v_time_1019_, 1);
    v_second_1022_ = crate::leanh::lean_ctor_get(v_time_1019_, 2);
    v___x_1023_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__1,
    );
    v___x_1024_ = lean_int_mul(v_hour_1020_, v___x_1023_);
    v___x_1025_ = lean_int_add(v___x_1024_, v_minute_1021_);
    crate::leanh::lean_dec(v___x_1024_);
    v___x_1026_ = lean_int_div(v_second_1022_, v___x_1023_);
    v___x_1027_ = lean_int_add(v___x_1025_, v___x_1026_);
    crate::leanh::lean_dec(v___x_1026_);
    crate::leanh::lean_dec(v___x_1025_);
    return v___x_1027_;
}
pub unsafe fn l_Std_Time_PlainTime_toMinutes___boxed(
    mut v_time_1028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Std_Time_PlainTime_toMinutes(v_time_1028_);
    crate::leanh::lean_dec_ref(v_time_1028_);
    return v_res_1029_;
}
pub unsafe fn l_Std_Time_PlainTime_toHours(
    mut v_time_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_1031_ = crate::leanh::lean_ctor_get(v_time_1030_, 0);
    crate::leanh::lean_inc(v_hour_1031_);
    return v_hour_1031_;
}
pub unsafe fn l_Std_Time_PlainTime_toHours___boxed(
    mut v_time_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Std_Time_PlainTime_toHours(v_time_1032_);
    crate::leanh::lean_dec_ref(v_time_1032_);
    return v_res_1033_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_1035_ = lean_nat_to_int(v___x_1034_);
    return v___x_1035_;
}
pub unsafe fn l_Std_Time_PlainTime_ofNanoseconds(
    mut v_nanos_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remainingNanos_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hours_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minutes_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1038_ = lean_int_ediv(v_nanos_1036_, v___x_1037_);
    v_remainingNanos_1039_ = lean_int_emod(v_nanos_1036_, v___x_1037_);
    v___x_1040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__0,
    );
    v___x_1041_ = lean_int_ediv(v___x_1038_, v___x_1040_);
    v___x_1042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0,
    );
    v_hours_1043_ = lean_int_emod(v___x_1041_, v___x_1042_);
    crate::leanh::lean_dec(v___x_1041_);
    v___x_1044_ = lean_int_emod(v___x_1038_, v___x_1040_);
    v___x_1045_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__1,
    );
    v_minutes_1046_ = lean_int_ediv(v___x_1044_, v___x_1045_);
    crate::leanh::lean_dec(v___x_1044_);
    v_seconds_1047_ = lean_int_emod(v___x_1038_, v___x_1045_);
    crate::leanh::lean_dec(v___x_1038_);
    v___x_1048_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1048_, 0, v_hours_1043_);
    crate::leanh::lean_ctor_set(v___x_1048_, 1, v_minutes_1046_);
    crate::leanh::lean_ctor_set(v___x_1048_, 2, v_seconds_1047_);
    crate::leanh::lean_ctor_set(v___x_1048_, 3, v_remainingNanos_1039_);
    return v___x_1048_;
}
pub unsafe fn l_Std_Time_PlainTime_ofNanoseconds___boxed(
    mut v_nanos_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1049_);
    crate::leanh::lean_dec(v_nanos_1049_);
    return v_res_1050_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMilliseconds(
    mut v_millis_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_1053_ = lean_int_mul(v_millis_1051_, v___x_1052_);
    v___x_1054_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1053_);
    crate::leanh::lean_dec(v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMilliseconds___boxed(
    mut v_millis_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Std_Time_PlainTime_ofMilliseconds(v_millis_1055_);
    crate::leanh::lean_dec(v_millis_1055_);
    return v_res_1056_;
}
pub unsafe fn l_Std_Time_PlainTime_ofSeconds(
    mut v_secs_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1059_ = lean_int_mul(v_secs_1057_, v___x_1058_);
    v___x_1060_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1059_);
    crate::leanh::lean_dec(v___x_1059_);
    return v___x_1060_;
}
pub unsafe fn l_Std_Time_PlainTime_ofSeconds___boxed(
    mut v_secs_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Std_Time_PlainTime_ofSeconds(v_secs_1061_);
    crate::leanh::lean_dec(v_secs_1061_);
    return v_res_1062_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMinutes(
    mut v_secs_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_1065_ = lean_int_mul(v_secs_1063_, v___x_1064_);
    v___x_1066_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1065_);
    crate::leanh::lean_dec(v___x_1065_);
    return v___x_1066_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMinutes___boxed(
    mut v_secs_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Std_Time_PlainTime_ofMinutes(v_secs_1067_);
    crate::leanh::lean_dec(v_secs_1067_);
    return v_res_1068_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHours(
    mut v_hour_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_1071_ = lean_int_mul(v_hour_1069_, v___x_1070_);
    v___x_1072_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1071_);
    crate::leanh::lean_dec(v___x_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHours___boxed(
    mut v_hour_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Std_Time_PlainTime_ofHours(v_hour_1073_);
    crate::leanh::lean_dec(v_hour_1073_);
    return v_res_1074_;
}
pub unsafe fn l_Std_Time_PlainTime_addSeconds(
    mut v_time_1075_: *mut crate::leanh::LeanObject,
    mut v_secondsToAdd_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalSeconds_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1075_);
    v___x_1078_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1079_ = lean_int_mul(v_secondsToAdd_1076_, v___x_1078_);
    v_totalSeconds_1080_ = lean_int_add(v___x_1077_, v___x_1079_);
    crate::leanh::lean_dec(v___x_1079_);
    crate::leanh::lean_dec(v___x_1077_);
    v___x_1081_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_1080_);
    crate::leanh::lean_dec(v_totalSeconds_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Std_Time_PlainTime_addSeconds___boxed(
    mut v_time_1082_: *mut crate::leanh::LeanObject,
    mut v_secondsToAdd_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Std_Time_PlainTime_addSeconds(v_time_1082_, v_secondsToAdd_1083_);
    crate::leanh::lean_dec(v_secondsToAdd_1083_);
    crate::leanh::lean_dec_ref(v_time_1082_);
    return v_res_1084_;
}
pub unsafe fn l_Std_Time_PlainTime_subSeconds(
    mut v_time_1085_: *mut crate::leanh::LeanObject,
    mut v_secondsToSub_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalSeconds_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = lean_int_neg(v_secondsToSub_1086_);
    v___x_1088_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1085_);
    v___x_1089_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1090_ = lean_int_mul(v___x_1087_, v___x_1089_);
    crate::leanh::lean_dec(v___x_1087_);
    v_totalSeconds_1091_ = lean_int_add(v___x_1088_, v___x_1090_);
    crate::leanh::lean_dec(v___x_1090_);
    crate::leanh::lean_dec(v___x_1088_);
    v___x_1092_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_1091_);
    crate::leanh::lean_dec(v_totalSeconds_1091_);
    return v___x_1092_;
}
pub unsafe fn l_Std_Time_PlainTime_subSeconds___boxed(
    mut v_time_1093_: *mut crate::leanh::LeanObject,
    mut v_secondsToSub_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Std_Time_PlainTime_subSeconds(v_time_1093_, v_secondsToSub_1094_);
    crate::leanh::lean_dec(v_secondsToSub_1094_);
    crate::leanh::lean_dec_ref(v_time_1093_);
    return v_res_1095_;
}
pub unsafe fn l_Std_Time_PlainTime_addMinutes(
    mut v_time_1096_: *mut crate::leanh::LeanObject,
    mut v_minutesToAdd_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_total_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1096_);
    v___x_1099_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_1100_ = lean_int_mul(v_minutesToAdd_1097_, v___x_1099_);
    v_total_1101_ = lean_int_add(v___x_1098_, v___x_1100_);
    crate::leanh::lean_dec(v___x_1100_);
    crate::leanh::lean_dec(v___x_1098_);
    v___x_1102_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1101_);
    crate::leanh::lean_dec(v_total_1101_);
    return v___x_1102_;
}
pub unsafe fn l_Std_Time_PlainTime_addMinutes___boxed(
    mut v_time_1103_: *mut crate::leanh::LeanObject,
    mut v_minutesToAdd_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ = l_Std_Time_PlainTime_addMinutes(v_time_1103_, v_minutesToAdd_1104_);
    crate::leanh::lean_dec(v_minutesToAdd_1104_);
    crate::leanh::lean_dec_ref(v_time_1103_);
    return v_res_1105_;
}
pub unsafe fn l_Std_Time_PlainTime_subMinutes(
    mut v_time_1106_: *mut crate::leanh::LeanObject,
    mut v_minutesToSub_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_total_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = lean_int_neg(v_minutesToSub_1107_);
    v___x_1109_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1106_);
    v___x_1110_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_1111_ = lean_int_mul(v___x_1108_, v___x_1110_);
    crate::leanh::lean_dec(v___x_1108_);
    v_total_1112_ = lean_int_add(v___x_1109_, v___x_1111_);
    crate::leanh::lean_dec(v___x_1111_);
    crate::leanh::lean_dec(v___x_1109_);
    v___x_1113_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1112_);
    crate::leanh::lean_dec(v_total_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_Time_PlainTime_subMinutes___boxed(
    mut v_time_1114_: *mut crate::leanh::LeanObject,
    mut v_minutesToSub_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Std_Time_PlainTime_subMinutes(v_time_1114_, v_minutesToSub_1115_);
    crate::leanh::lean_dec(v_minutesToSub_1115_);
    crate::leanh::lean_dec_ref(v_time_1114_);
    return v_res_1116_;
}
pub unsafe fn l_Std_Time_PlainTime_addHours(
    mut v_time_1117_: *mut crate::leanh::LeanObject,
    mut v_hoursToAdd_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_total_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1117_);
    v___x_1120_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_1121_ = lean_int_mul(v_hoursToAdd_1118_, v___x_1120_);
    v_total_1122_ = lean_int_add(v___x_1119_, v___x_1121_);
    crate::leanh::lean_dec(v___x_1121_);
    crate::leanh::lean_dec(v___x_1119_);
    v___x_1123_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1122_);
    crate::leanh::lean_dec(v_total_1122_);
    return v___x_1123_;
}
pub unsafe fn l_Std_Time_PlainTime_addHours___boxed(
    mut v_time_1124_: *mut crate::leanh::LeanObject,
    mut v_hoursToAdd_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Std_Time_PlainTime_addHours(v_time_1124_, v_hoursToAdd_1125_);
    crate::leanh::lean_dec(v_hoursToAdd_1125_);
    crate::leanh::lean_dec_ref(v_time_1124_);
    return v_res_1126_;
}
pub unsafe fn l_Std_Time_PlainTime_subHours(
    mut v_time_1127_: *mut crate::leanh::LeanObject,
    mut v_hoursToSub_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_total_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = lean_int_neg(v_hoursToSub_1128_);
    v___x_1130_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1127_);
    v___x_1131_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_1132_ = lean_int_mul(v___x_1129_, v___x_1131_);
    crate::leanh::lean_dec(v___x_1129_);
    v_total_1133_ = lean_int_add(v___x_1130_, v___x_1132_);
    crate::leanh::lean_dec(v___x_1132_);
    crate::leanh::lean_dec(v___x_1130_);
    v___x_1134_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1133_);
    crate::leanh::lean_dec(v_total_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Std_Time_PlainTime_subHours___boxed(
    mut v_time_1135_: *mut crate::leanh::LeanObject,
    mut v_hoursToSub_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Std_Time_PlainTime_subHours(v_time_1135_, v_hoursToSub_1136_);
    crate::leanh::lean_dec(v_hoursToSub_1136_);
    crate::leanh::lean_dec_ref(v_time_1135_);
    return v_res_1137_;
}
pub unsafe fn l_Std_Time_PlainTime_addNanoseconds(
    mut v_time_1138_: *mut crate::leanh::LeanObject,
    mut v_nanosToAdd_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_total_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1138_);
    v_total_1141_ = lean_int_add(v___x_1140_, v_nanosToAdd_1139_);
    crate::leanh::lean_dec(v___x_1140_);
    v___x_1142_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1141_);
    crate::leanh::lean_dec(v_total_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Std_Time_PlainTime_addNanoseconds___boxed(
    mut v_time_1143_: *mut crate::leanh::LeanObject,
    mut v_nanosToAdd_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Std_Time_PlainTime_addNanoseconds(v_time_1143_, v_nanosToAdd_1144_);
    crate::leanh::lean_dec(v_nanosToAdd_1144_);
    crate::leanh::lean_dec_ref(v_time_1143_);
    return v_res_1145_;
}
pub unsafe fn l_Std_Time_PlainTime_subNanoseconds(
    mut v_time_1146_: *mut crate::leanh::LeanObject,
    mut v_nanosToSub_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = lean_int_neg(v_nanosToSub_1147_);
    v___x_1149_ = l_Std_Time_PlainTime_addNanoseconds(v_time_1146_, v___x_1148_);
    crate::leanh::lean_dec(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn l_Std_Time_PlainTime_subNanoseconds___boxed(
    mut v_time_1150_: *mut crate::leanh::LeanObject,
    mut v_nanosToSub_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1152_ = l_Std_Time_PlainTime_subNanoseconds(v_time_1150_, v_nanosToSub_1151_);
    crate::leanh::lean_dec(v_nanosToSub_1151_);
    crate::leanh::lean_dec_ref(v_time_1150_);
    return v_res_1152_;
}
pub unsafe fn l_Std_Time_PlainTime_addMilliseconds(
    mut v_time_1153_: *mut crate::leanh::LeanObject,
    mut v_millisToAdd_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_total_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1153_);
    v_total_1156_ = lean_int_add(v___x_1155_, v_millisToAdd_1154_);
    crate::leanh::lean_dec(v___x_1155_);
    v___x_1157_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_1158_ = lean_int_mul(v_total_1156_, v___x_1157_);
    crate::leanh::lean_dec(v_total_1156_);
    v___x_1159_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1158_);
    crate::leanh::lean_dec(v___x_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_Time_PlainTime_addMilliseconds___boxed(
    mut v_time_1160_: *mut crate::leanh::LeanObject,
    mut v_millisToAdd_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_Time_PlainTime_addMilliseconds(v_time_1160_, v_millisToAdd_1161_);
    crate::leanh::lean_dec(v_millisToAdd_1161_);
    crate::leanh::lean_dec_ref(v_time_1160_);
    return v_res_1162_;
}
pub unsafe fn l_Std_Time_PlainTime_subMilliseconds(
    mut v_time_1163_: *mut crate::leanh::LeanObject,
    mut v_millisToSub_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1165_ = lean_int_neg(v_millisToSub_1164_);
    v___x_1166_ = l_Std_Time_PlainTime_addMilliseconds(v_time_1163_, v___x_1165_);
    crate::leanh::lean_dec(v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_Time_PlainTime_subMilliseconds___boxed(
    mut v_time_1167_: *mut crate::leanh::LeanObject,
    mut v_millisToSub_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Std_Time_PlainTime_subMilliseconds(v_time_1167_, v_millisToSub_1168_);
    crate::leanh::lean_dec(v_millisToSub_1168_);
    crate::leanh::lean_dec_ref(v_time_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Std_Time_PlainTime_withSeconds(
    mut v_pt_1170_: *mut crate::leanh::LeanObject,
    mut v_second_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_unused_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1172_ = crate::leanh::lean_ctor_get(v_pt_1170_, 0);
                v_minute_1173_ = crate::leanh::lean_ctor_get(v_pt_1170_, 1);
                v_nanosecond_1174_ = crate::leanh::lean_ctor_get(v_pt_1170_, 3);
                v_isSharedCheck_1181_ = (!crate::leanh::lean_is_exclusive(v_pt_1170_)) as u8;
                if v_isSharedCheck_1181_ == 0 {
                    v_unused_1182_ = crate::leanh::lean_ctor_get(v_pt_1170_, 2);
                    crate::leanh::lean_dec(v_unused_1182_);
                    v___x_1176_ = v_pt_1170_;
                    v_isShared_1177_ = v_isSharedCheck_1181_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_1174_);
                    crate::leanh::lean_inc(v_minute_1173_);
                    crate::leanh::lean_inc(v_hour_1172_);
                    crate::leanh::lean_dec(v_pt_1170_);
                    v___x_1176_ = crate::leanh::lean_box(0);
                    v_isShared_1177_ = v_isSharedCheck_1181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1176_, 2, v_second_1171_);
                    v___x_1179_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_hour_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_minute_1173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_second_1171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_nanosecond_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_withMinutes(
    mut v_pt_1183_: *mut crate::leanh::LeanObject,
    mut v_minute_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut v_unused_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1185_ = crate::leanh::lean_ctor_get(v_pt_1183_, 0);
                v_second_1186_ = crate::leanh::lean_ctor_get(v_pt_1183_, 2);
                v_nanosecond_1187_ = crate::leanh::lean_ctor_get(v_pt_1183_, 3);
                v_isSharedCheck_1194_ = (!crate::leanh::lean_is_exclusive(v_pt_1183_)) as u8;
                if v_isSharedCheck_1194_ == 0 {
                    v_unused_1195_ = crate::leanh::lean_ctor_get(v_pt_1183_, 1);
                    crate::leanh::lean_dec(v_unused_1195_);
                    v___x_1189_ = v_pt_1183_;
                    v_isShared_1190_ = v_isSharedCheck_1194_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_1187_);
                    crate::leanh::lean_inc(v_second_1186_);
                    crate::leanh::lean_inc(v_hour_1185_);
                    crate::leanh::lean_dec(v_pt_1183_);
                    v___x_1189_ = crate::leanh::lean_box(0);
                    v_isShared_1190_ = v_isSharedCheck_1194_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1189_, 1, v_minute_1184_);
                    v___x_1192_ = v___x_1189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_hour_1185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_minute_1184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_second_1186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_nanosecond_1187_);
                    v___x_1192_ = v_reuseFailAlloc_1193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_withMilliseconds(
    mut v_pt_1196_: *mut crate::leanh::LeanObject,
    mut v_millis_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1198_ = crate::leanh::lean_ctor_get(v_pt_1196_, 0);
                v_minute_1199_ = crate::leanh::lean_ctor_get(v_pt_1196_, 1);
                v_second_1200_ = crate::leanh::lean_ctor_get(v_pt_1196_, 2);
                v_nanosecond_1201_ = crate::leanh::lean_ctor_get(v_pt_1196_, 3);
                v_isSharedCheck_1213_ = (!crate::leanh::lean_is_exclusive(v_pt_1196_)) as u8;
                if v_isSharedCheck_1213_ == 0 {
                    v___x_1203_ = v_pt_1196_;
                    v_isShared_1204_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_1201_);
                    crate::leanh::lean_inc(v_second_1200_);
                    crate::leanh::lean_inc(v_minute_1199_);
                    crate::leanh::lean_inc(v_hour_1198_);
                    crate::leanh::lean_dec(v_pt_1196_);
                    v___x_1203_ = crate::leanh::lean_box(0);
                    v_isShared_1204_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1205_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2_once),
                    _init_l_Std_Time_PlainTime_toMilliseconds___closed__2,
                );
                v___x_1206_ = lean_int_emod(v_nanosecond_1201_, v___x_1205_);
                crate::leanh::lean_dec(v_nanosecond_1201_);
                v___x_1207_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
                    _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
                );
                v___x_1208_ = lean_int_mul(v_millis_1197_, v___x_1207_);
                v___x_1209_ = lean_int_add(v___x_1208_, v___x_1206_);
                crate::leanh::lean_dec(v___x_1206_);
                crate::leanh::lean_dec(v___x_1208_);
                if v_isShared_1204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1203_, 3, v___x_1209_);
                    v___x_1211_ = v___x_1203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_hour_1198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_minute_1199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_second_1200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 3, v___x_1209_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_withMilliseconds___boxed(
    mut v_pt_1214_: *mut crate::leanh::LeanObject,
    mut v_millis_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Std_Time_PlainTime_withMilliseconds(v_pt_1214_, v_millis_1215_);
    crate::leanh::lean_dec(v_millis_1215_);
    return v_res_1216_;
}
pub unsafe fn l_Std_Time_PlainTime_withNanoseconds(
    mut v_pt_1217_: *mut crate::leanh::LeanObject,
    mut v_nano_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_unused_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1219_ = crate::leanh::lean_ctor_get(v_pt_1217_, 0);
                v_minute_1220_ = crate::leanh::lean_ctor_get(v_pt_1217_, 1);
                v_second_1221_ = crate::leanh::lean_ctor_get(v_pt_1217_, 2);
                v_isSharedCheck_1228_ = (!crate::leanh::lean_is_exclusive(v_pt_1217_)) as u8;
                if v_isSharedCheck_1228_ == 0 {
                    v_unused_1229_ = crate::leanh::lean_ctor_get(v_pt_1217_, 3);
                    crate::leanh::lean_dec(v_unused_1229_);
                    v___x_1223_ = v_pt_1217_;
                    v_isShared_1224_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_second_1221_);
                    crate::leanh::lean_inc(v_minute_1220_);
                    crate::leanh::lean_inc(v_hour_1219_);
                    crate::leanh::lean_dec(v_pt_1217_);
                    v___x_1223_ = crate::leanh::lean_box(0);
                    v_isShared_1224_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1223_, 3, v_nano_1218_);
                    v___x_1226_ = v___x_1223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_hour_1219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_minute_1220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_second_1221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_nano_1218_);
                    v___x_1226_ = v_reuseFailAlloc_1227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_withHours(
    mut v_pt_1230_: *mut crate::leanh::LeanObject,
    mut v_hour_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minute_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut v_unused_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_minute_1232_ = crate::leanh::lean_ctor_get(v_pt_1230_, 1);
                v_second_1233_ = crate::leanh::lean_ctor_get(v_pt_1230_, 2);
                v_nanosecond_1234_ = crate::leanh::lean_ctor_get(v_pt_1230_, 3);
                v_isSharedCheck_1241_ = (!crate::leanh::lean_is_exclusive(v_pt_1230_)) as u8;
                if v_isSharedCheck_1241_ == 0 {
                    v_unused_1242_ = crate::leanh::lean_ctor_get(v_pt_1230_, 0);
                    crate::leanh::lean_dec(v_unused_1242_);
                    v___x_1236_ = v_pt_1230_;
                    v_isShared_1237_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_1234_);
                    crate::leanh::lean_inc(v_second_1233_);
                    crate::leanh::lean_inc(v_minute_1232_);
                    crate::leanh::lean_dec(v_pt_1230_);
                    v___x_1236_ = crate::leanh::lean_box(0);
                    v_isShared_1237_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1237_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1236_, 0, v_hour_1231_);
                    v___x_1239_ = v___x_1236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_hour_1231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_minute_1232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_second_1233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_nanosecond_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_millisecond(
    mut v_pt_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nanosecond_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nanosecond_1244_ = crate::leanh::lean_ctor_get(v_pt_1243_, 3);
    v___x_1245_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_1246_ = lean_int_ediv(v_nanosecond_1244_, v___x_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Std_Time_PlainTime_millisecond___boxed(
    mut v_pt_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Std_Time_PlainTime_millisecond(v_pt_1247_);
    crate::leanh::lean_dec_ref(v_pt_1247_);
    return v_res_1248_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_PlainTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedPlainTime = _init_l_Std_Time_instInhabitedPlainTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedPlainTime);
    l_Std_Time_PlainTime_midnight = _init_l_Std_Time_PlainTime_midnight();
    crate::leanh::lean_mark_persistent(l_Std_Time_PlainTime_midnight);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_PlainTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_PlainTime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_PlainTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_PlainTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_PlainTime(builtin);
}
