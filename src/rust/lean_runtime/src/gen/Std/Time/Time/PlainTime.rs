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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{
    lean_int_div, lean_int_ediv, lean_int_emod,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::lean_nat_mod;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_cstr_to_nat, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once,
    lean_unsigned_to_nat,
};
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value: LeanStringObject<3> =
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
        m_data: [123, 32, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value: LeanStringObject<5> =
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
        m_data: [104, 111, 117, 114, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value: LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value: LeanStringObject<7> =
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
        m_data: [109, 105, 110, 117, 116, 101, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value: LeanStringObject<7> =
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
        m_data: [115, 101, 99, 111, 110, 100, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__16_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value: LeanStringObject<3> =
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
        m_data: [32, 125, 0],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainTime_repr___redArg___closed__22_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime_repr___redArg___closed__22_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainTime_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainTime___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instReprPlainTime_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprPlainTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instReprPlainTime: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainTime___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instInhabitedPlainTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainTime___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainTime___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainTime: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instOrdPlainTime___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_instOrdPlainTime___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__5_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainTime___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__6_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__7_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__7_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__8_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__5_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__1_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__8_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__9_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Second_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Time_instOrdPlainTime___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__9_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__10_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__9_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__10_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__11_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__11_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__12_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__10_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__11_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__12_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__13_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__8_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__12_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__13_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainTime___closed__14_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__7_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__13_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainTime___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__14_value) as *mut LeanObject;
pub static mut l_Std_Time_instOrdPlainTime: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainTime___closed__14_value) as *mut LeanObject;
static mut l_Std_Time_PlainTime_midnight___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_midnight___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_midnight___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_PlainTime_midnight: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toMilliseconds___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toMilliseconds___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toMilliseconds___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toMilliseconds___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toMilliseconds___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toNanoseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toNanoseconds___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toNanoseconds___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toNanoseconds___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toNanoseconds___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toNanoseconds___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toSeconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toSeconds___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_toSeconds___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_toSeconds___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainTime_ofNanoseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_ofNanoseconds___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_PlainTime_instHAddOffset___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_addNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_subNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_addMilliseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHAddOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_subMilliseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHSubOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_addSeconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHAddOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_subSeconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHSubOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_addMinutes___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHAddOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_subMinutes___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHSubOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_addHours___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHAddOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHAddOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_PlainTime_subHours___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instHSubOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainTime_instHSubOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprPlainTime_repr_spec__0(
    mut v_a_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    v___x_636_ = lean_nat_to_int(v_a_635_);
    return v___x_636_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    v___x_650_ = lean_unsigned_to_nat(8);
    v___x_651_ = lean_nat_to_int(v___x_650_);
    return v___x_651_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    v___x_658_ = lean_unsigned_to_nat(10);
    v___x_659_ = lean_nat_to_int(v___x_658_);
    return v___x_659_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    v___x_666_ = lean_unsigned_to_nat(14);
    v___x_667_ = lean_nat_to_int(v___x_666_);
    return v___x_667_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__19() -> *mut LeanObject {
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_669_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__0;
    v___x_670_ = lean_string_length(v___x_669_);
    return v___x_670_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__20() -> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    v___x_671_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__19_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__19,
    );
    v___x_672_ = lean_nat_to_int(v___x_671_);
    return v___x_672_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23() -> *mut LeanObject {
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_677_ = lean_unsigned_to_nat(0);
    v___x_678_ = lean_nat_to_int(v___x_677_);
    return v___x_678_;
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr___redArg(
    mut v_x_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_680_ = lean_ctor_get(v_x_679_, 0);
                v_minute_681_ = lean_ctor_get(v_x_679_, 1);
                v_second_682_ = lean_ctor_get(v_x_679_, 2);
                v_nanosecond_683_ = lean_ctor_get(v_x_679_, 3);
                v___x_684_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__5;
                v___x_685_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__6;
                v___x_686_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__7,
                );
                v___x_687_ = lean_unsigned_to_nat(0);
                v___x_688_ = l_Std_Time_Hour_instReprOrdinal___lam__0(v_hour_680_, v___x_687_);
                v___x_689_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_689_, 0, v___x_686_);
                lean_ctor_set(v___x_689_, 1, v___x_688_);
                v___x_690_ = 0;
                v___x_691_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_691_, 0, v___x_689_);
                lean_ctor_set_uint8(
                    v___x_691_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_692_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_692_, 0, v___x_685_);
                lean_ctor_set(v___x_692_, 1, v___x_691_);
                v___x_693_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__9;
                v___x_694_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_694_, 0, v___x_692_);
                lean_ctor_set(v___x_694_, 1, v___x_693_);
                v___x_695_ = lean_box(1);
                v___x_696_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_696_, 0, v___x_694_);
                lean_ctor_set(v___x_696_, 1, v___x_695_);
                v___x_697_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__11;
                v___x_698_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_698_, 0, v___x_696_);
                lean_ctor_set(v___x_698_, 1, v___x_697_);
                v___x_699_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_699_, 0, v___x_698_);
                lean_ctor_set(v___x_699_, 1, v___x_684_);
                v___x_700_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__12_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__12,
                );
                v___x_701_ = l_Std_Time_Minute_instReprOrdinal___lam__0(v_minute_681_, v___x_687_);
                v___x_702_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_702_, 0, v___x_700_);
                lean_ctor_set(v___x_702_, 1, v___x_701_);
                v___x_703_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_703_, 0, v___x_702_);
                lean_ctor_set_uint8(
                    v___x_703_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_704_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_704_, 0, v___x_699_);
                lean_ctor_set(v___x_704_, 1, v___x_703_);
                v___x_705_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_705_, 0, v___x_704_);
                lean_ctor_set(v___x_705_, 1, v___x_693_);
                v___x_706_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_706_, 0, v___x_705_);
                lean_ctor_set(v___x_706_, 1, v___x_695_);
                v___x_707_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__14;
                v___x_708_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_708_, 0, v___x_706_);
                lean_ctor_set(v___x_708_, 1, v___x_707_);
                v___x_709_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_709_, 0, v___x_708_);
                lean_ctor_set(v___x_709_, 1, v___x_684_);
                v___x_732_ = lean_obj_once(
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
                    v___x_735_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_735_, 0, v___x_734_);
                    v___y_711_ = v___x_735_;
                    state = 1;
                    continue;
                } else {
                    v___x_736_ = l_Int_repr(v_second_682_);
                    v___x_737_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_737_, 0, v___x_736_);
                    v___x_738_ = l_Repr_addAppParen(v___x_737_, v___x_687_);
                    v___y_711_ = v___x_738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_712_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_712_, 0, v___x_700_);
                lean_ctor_set(v___x_712_, 1, v___y_711_);
                v___x_713_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_713_, 0, v___x_712_);
                lean_ctor_set_uint8(
                    v___x_713_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_714_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_714_, 0, v___x_709_);
                lean_ctor_set(v___x_714_, 1, v___x_713_);
                v___x_715_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_715_, 0, v___x_714_);
                lean_ctor_set(v___x_715_, 1, v___x_693_);
                v___x_716_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_716_, 0, v___x_715_);
                lean_ctor_set(v___x_716_, 1, v___x_695_);
                v___x_717_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__16;
                v___x_718_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_718_, 0, v___x_716_);
                lean_ctor_set(v___x_718_, 1, v___x_717_);
                v___x_719_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_719_, 0, v___x_718_);
                lean_ctor_set(v___x_719_, 1, v___x_684_);
                v___x_720_ = lean_obj_once(
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
                v___x_722_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_722_, 0, v___x_720_);
                lean_ctor_set(v___x_722_, 1, v___x_721_);
                v___x_723_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_723_, 0, v___x_722_);
                lean_ctor_set_uint8(
                    v___x_723_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                v___x_724_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_724_, 0, v___x_719_);
                lean_ctor_set(v___x_724_, 1, v___x_723_);
                v___x_725_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainTime_repr___redArg___closed__20_once
                    ),
                    _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__20,
                );
                v___x_726_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__21;
                v___x_727_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_727_, 0, v___x_726_);
                lean_ctor_set(v___x_727_, 1, v___x_724_);
                v___x_728_ = l_Std_Time_instReprPlainTime_repr___redArg___closed__22;
                v___x_729_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_729_, 0, v___x_727_);
                lean_ctor_set(v___x_729_, 1, v___x_728_);
                v___x_730_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_730_, 0, v___x_725_);
                lean_ctor_set(v___x_730_, 1, v___x_729_);
                v___x_731_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_731_, 0, v___x_730_);
                lean_ctor_set_uint8(
                    v___x_731_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_690_,
                );
                return v___x_731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr___redArg___boxed(
    mut v_x_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_740_: *mut LeanObject = core::ptr::null_mut();
    v_res_740_ = l_Std_Time_instReprPlainTime_repr___redArg(v_x_739_);
    lean_dec_ref(v_x_739_);
    return v_res_740_;
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr(
    mut v_x_741_: *mut LeanObject,
    mut v_prec_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = l_Std_Time_instReprPlainTime_repr___redArg(v_x_741_);
    return v___x_743_;
}
pub unsafe fn l_Std_Time_instReprPlainTime_repr___boxed(
    mut v_x_744_: *mut LeanObject,
    mut v_prec_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_746_: *mut LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Std_Time_instReprPlainTime_repr(v_x_744_, v_prec_745_);
    lean_dec(v_prec_745_);
    lean_dec_ref(v_x_744_);
    return v_res_746_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime_decEq(
    mut v_x_749_: *mut LeanObject,
    mut v_x_750_: *mut LeanObject,
) -> u8 {
    let mut v_hour_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hour_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u8 = 0;
    v_hour_751_ = lean_ctor_get(v_x_749_, 0);
    v_minute_752_ = lean_ctor_get(v_x_749_, 1);
    v_second_753_ = lean_ctor_get(v_x_749_, 2);
    v_nanosecond_754_ = lean_ctor_get(v_x_749_, 3);
    v_hour_755_ = lean_ctor_get(v_x_750_, 0);
    v_minute_756_ = lean_ctor_get(v_x_750_, 1);
    v_second_757_ = lean_ctor_get(v_x_750_, 2);
    v_nanosecond_758_ = lean_ctor_get(v_x_750_, 3);
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
    mut v_x_763_: *mut LeanObject,
    mut v_x_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_763_, v_x_764_);
    lean_dec_ref(v_x_764_);
    lean_dec_ref(v_x_763_);
    v_r_766_ = lean_box((v_res_765_) as usize);
    return v_r_766_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime(
    mut v_x_767_: *mut LeanObject,
    mut v_x_768_: *mut LeanObject,
) -> u8 {
    let mut v___x_769_: u8 = 0;
    v___x_769_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_767_, v_x_768_);
    return v___x_769_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainTime___boxed(
    mut v_x_770_: *mut LeanObject,
    mut v_x_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Std_Time_instDecidableEqPlainTime(v_x_770_, v_x_771_);
    lean_dec_ref(v_x_771_);
    lean_dec_ref(v_x_770_);
    v_r_773_ = lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__0() -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = lean_unsigned_to_nat(23);
    v___x_775_ = lean_nat_to_int(v___x_774_);
    return v___x_775_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__1() -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__0,
    );
    v___x_777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_778_ = lean_int_add(v___x_777_, v___x_776_);
    return v___x_778_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__2() -> *mut LeanObject {
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v___x_779_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_780_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__1,
    );
    v___x_781_ = lean_int_sub(v___x_780_, v___x_779_);
    return v___x_781_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__3() -> *mut LeanObject {
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    v___x_782_ = lean_unsigned_to_nat(1);
    v___x_783_ = lean_nat_to_int(v___x_782_);
    return v___x_783_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__4() -> *mut LeanObject {
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_786_: *mut LeanObject = core::ptr::null_mut();
    v___x_784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_785_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__2_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__2,
    );
    v_range_786_ = lean_int_add(v___x_785_, v___x_784_);
    return v_range_786_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__5() -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_788_ = lean_int_sub(v___x_787_, v___x_787_);
    return v___x_788_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__6() -> *mut LeanObject {
    let mut v_range_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    v_range_789_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__4,
    );
    v___x_790_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_791_ = lean_int_emod(v___x_790_, v_range_789_);
    return v___x_791_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__7() -> *mut LeanObject {
    let mut v_range_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    v_range_792_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__4,
    );
    v___x_793_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__6,
    );
    v___x_794_ = lean_int_add(v___x_793_, v_range_792_);
    return v___x_794_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__8() -> *mut LeanObject {
    let mut v_range_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v_range_795_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__4,
    );
    v___x_796_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__7_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__7,
    );
    v___x_797_ = lean_int_emod(v___x_796_, v_range_795_);
    return v___x_797_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__9() -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_799_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__8_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__8,
    );
    v___x_800_ = lean_int_add(v___x_799_, v___x_798_);
    return v___x_800_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__10() -> *mut LeanObject {
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v___x_801_ = lean_unsigned_to_nat(59);
    v___x_802_ = lean_nat_to_int(v___x_801_);
    return v___x_802_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__11() -> *mut LeanObject {
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__10_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__10,
    );
    v___x_804_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_805_ = lean_int_add(v___x_804_, v___x_803_);
    return v___x_805_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__12() -> *mut LeanObject {
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_806_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_807_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__11,
    );
    v___x_808_ = lean_int_sub(v___x_807_, v___x_806_);
    return v___x_808_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__13() -> *mut LeanObject {
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_809_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_810_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__12_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__12,
    );
    v_range_811_ = lean_int_add(v___x_810_, v___x_809_);
    return v_range_811_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__14() -> *mut LeanObject {
    let mut v_range_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v_range_812_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__13,
    );
    v___x_813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_814_ = lean_int_emod(v___x_813_, v_range_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__15() -> *mut LeanObject {
    let mut v_range_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v_range_815_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__13,
    );
    v___x_816_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__14,
    );
    v___x_817_ = lean_int_add(v___x_816_, v_range_815_);
    return v___x_817_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__16() -> *mut LeanObject {
    let mut v_range_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    v_range_818_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__13,
    );
    v___x_819_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__15_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__15,
    );
    v___x_820_ = lean_int_emod(v___x_819_, v_range_818_);
    return v___x_820_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__17() -> *mut LeanObject {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    v___x_821_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_822_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__16_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__16,
    );
    v___x_823_ = lean_int_add(v___x_822_, v___x_821_);
    return v___x_823_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__18() -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: u8 = 0;
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = lean_unsigned_to_nat(0);
    v___x_825_ = 1;
    v___x_826_ = l_Std_Time_Second_instOfNatOrdinal(v___x_825_, v___x_824_);
    return v___x_826_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime___closed__19() -> *mut LeanObject {
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_827_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_828_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__18,
    );
    v___x_829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__17,
    );
    v___x_830_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__9,
    );
    v___x_831_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_831_, 0, v___x_830_);
    lean_ctor_set(v___x_831_, 1, v___x_829_);
    lean_ctor_set(v___x_831_, 2, v___x_828_);
    lean_ctor_set(v___x_831_, 3, v___x_827_);
    return v___x_831_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainTime() -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__19_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__19,
    );
    return v___x_832_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__0(
    mut v_x_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_834_: *mut LeanObject = core::ptr::null_mut();
    v_hour_834_ = lean_ctor_get(v_x_833_, 0);
    lean_inc(v_hour_834_);
    return v_hour_834_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__0___boxed(
    mut v_x_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_836_: *mut LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Std_Time_instOrdPlainTime___lam__0(v_x_835_);
    lean_dec_ref(v_x_835_);
    return v_res_836_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__1(
    mut v_x_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minute_838_: *mut LeanObject = core::ptr::null_mut();
    v_minute_838_ = lean_ctor_get(v_x_837_, 1);
    lean_inc(v_minute_838_);
    return v_minute_838_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__1___boxed(
    mut v_x_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_840_: *mut LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Std_Time_instOrdPlainTime___lam__1(v_x_839_);
    lean_dec_ref(v_x_839_);
    return v_res_840_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__2(
    mut v_x_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_842_: *mut LeanObject = core::ptr::null_mut();
    v_second_842_ = lean_ctor_get(v_x_841_, 2);
    lean_inc(v_second_842_);
    return v_second_842_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__2___boxed(
    mut v_x_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_844_: *mut LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Std_Time_instOrdPlainTime___lam__2(v_x_843_);
    lean_dec_ref(v_x_843_);
    return v_res_844_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__3(
    mut v_x_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nanosecond_846_: *mut LeanObject = core::ptr::null_mut();
    v_nanosecond_846_ = lean_ctor_get(v_x_845_, 3);
    lean_inc(v_nanosecond_846_);
    return v_nanosecond_846_;
}
pub unsafe fn l_Std_Time_instOrdPlainTime___lam__3___boxed(
    mut v_x_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_848_: *mut LeanObject = core::ptr::null_mut();
    v_res_848_ = l_Std_Time_instOrdPlainTime___lam__3(v_x_847_);
    lean_dec_ref(v_x_847_);
    return v_res_848_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__0() -> *mut LeanObject {
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    v___x_881_ = lean_unsigned_to_nat(23);
    v___x_882_ = lean_nat_to_int(v___x_881_);
    return v___x_882_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__1() -> *mut LeanObject {
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_883_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__0_once),
        _init_l_Std_Time_PlainTime_midnight___closed__0,
    );
    v___x_884_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_885_ = lean_int_add(v___x_884_, v___x_883_);
    return v___x_885_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__2() -> *mut LeanObject {
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__1_once),
        _init_l_Std_Time_PlainTime_midnight___closed__1,
    );
    v___x_888_ = lean_int_sub(v___x_887_, v___x_886_);
    return v___x_888_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__3() -> *mut LeanObject {
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_891_: *mut LeanObject = core::ptr::null_mut();
    v___x_889_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_890_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__2_once),
        _init_l_Std_Time_PlainTime_midnight___closed__2,
    );
    v_range_891_ = lean_int_add(v___x_890_, v___x_889_);
    return v_range_891_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__4() -> *mut LeanObject {
    let mut v_range_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    v_range_892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3_once),
        _init_l_Std_Time_PlainTime_midnight___closed__3,
    );
    v___x_893_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_894_ = lean_int_emod(v___x_893_, v_range_892_);
    return v___x_894_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__5() -> *mut LeanObject {
    let mut v_range_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    v_range_895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3_once),
        _init_l_Std_Time_PlainTime_midnight___closed__3,
    );
    v___x_896_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__4_once),
        _init_l_Std_Time_PlainTime_midnight___closed__4,
    );
    v___x_897_ = lean_int_add(v___x_896_, v_range_895_);
    return v___x_897_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__6() -> *mut LeanObject {
    let mut v_range_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    v_range_898_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__3_once),
        _init_l_Std_Time_PlainTime_midnight___closed__3,
    );
    v___x_899_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__5_once),
        _init_l_Std_Time_PlainTime_midnight___closed__5,
    );
    v___x_900_ = lean_int_emod(v___x_899_, v_range_898_);
    return v___x_900_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__7() -> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    v___x_901_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_902_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__6_once),
        _init_l_Std_Time_PlainTime_midnight___closed__6,
    );
    v___x_903_ = lean_int_add(v___x_902_, v___x_901_);
    return v___x_903_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__8() -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___x_904_ = lean_unsigned_to_nat(59);
    v___x_905_ = lean_nat_to_int(v___x_904_);
    return v___x_905_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__9() -> *mut LeanObject {
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    v___x_906_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__8_once),
        _init_l_Std_Time_PlainTime_midnight___closed__8,
    );
    v___x_907_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_908_ = lean_int_add(v___x_907_, v___x_906_);
    return v___x_908_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__10() -> *mut LeanObject {
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_909_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_910_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__9_once),
        _init_l_Std_Time_PlainTime_midnight___closed__9,
    );
    v___x_911_ = lean_int_sub(v___x_910_, v___x_909_);
    return v___x_911_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__11() -> *mut LeanObject {
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_912_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__3,
    );
    v___x_913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__10_once),
        _init_l_Std_Time_PlainTime_midnight___closed__10,
    );
    v_range_914_ = lean_int_add(v___x_913_, v___x_912_);
    return v_range_914_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__12() -> *mut LeanObject {
    let mut v_range_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    v_range_915_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11_once),
        _init_l_Std_Time_PlainTime_midnight___closed__11,
    );
    v___x_916_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__5,
    );
    v___x_917_ = lean_int_emod(v___x_916_, v_range_915_);
    return v___x_917_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__13() -> *mut LeanObject {
    let mut v_range_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v_range_918_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11_once),
        _init_l_Std_Time_PlainTime_midnight___closed__11,
    );
    v___x_919_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__12_once),
        _init_l_Std_Time_PlainTime_midnight___closed__12,
    );
    v___x_920_ = lean_int_add(v___x_919_, v_range_918_);
    return v___x_920_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__14() -> *mut LeanObject {
    let mut v_range_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v_range_921_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__11_once),
        _init_l_Std_Time_PlainTime_midnight___closed__11,
    );
    v___x_922_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__13_once),
        _init_l_Std_Time_PlainTime_midnight___closed__13,
    );
    v___x_923_ = lean_int_emod(v___x_922_, v_range_921_);
    return v___x_923_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__15() -> *mut LeanObject {
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once),
        _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23,
    );
    v___x_925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__14_once),
        _init_l_Std_Time_PlainTime_midnight___closed__14,
    );
    v___x_926_ = lean_int_add(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__16() -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = lean_unsigned_to_nat(1000000000);
    v___x_928_ = lean_unsigned_to_nat(0);
    v___x_929_ = lean_nat_mod(v___x_928_, v___x_927_);
    return v___x_929_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__17() -> *mut LeanObject {
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    v___x_930_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16_once),
        _init_l_Std_Time_PlainTime_midnight___closed__16,
    );
    v___x_931_ = lean_nat_to_int(v___x_930_);
    return v___x_931_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight___closed__18() -> *mut LeanObject {
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    v___x_932_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__17_once),
        _init_l_Std_Time_PlainTime_midnight___closed__17,
    );
    v___x_933_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainTime___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainTime___closed__18,
    );
    v___x_934_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__15_once),
        _init_l_Std_Time_PlainTime_midnight___closed__15,
    );
    v___x_935_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__7_once),
        _init_l_Std_Time_PlainTime_midnight___closed__7,
    );
    v___x_936_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_936_, 0, v___x_935_);
    lean_ctor_set(v___x_936_, 1, v___x_934_);
    lean_ctor_set(v___x_936_, 2, v___x_933_);
    lean_ctor_set(v___x_936_, 3, v___x_932_);
    return v___x_936_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_midnight() -> *mut LeanObject {
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    v___x_937_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__18_once),
        _init_l_Std_Time_PlainTime_midnight___closed__18,
    );
    return v___x_937_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHourMinuteSecondsNano(
    mut v_hour_938_: *mut LeanObject,
    mut v_minute_939_: *mut LeanObject,
    mut v_second_940_: *mut LeanObject,
    mut v_nano_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    v___x_942_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_942_, 0, v_hour_938_);
    lean_ctor_set(v___x_942_, 1, v_minute_939_);
    lean_ctor_set(v___x_942_, 2, v_second_940_);
    lean_ctor_set(v___x_942_, 3, v_nano_941_);
    return v___x_942_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0() -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_midnight___closed__16_once),
        _init_l_Std_Time_PlainTime_midnight___closed__16,
    );
    v___x_944_ = lean_nat_to_int(v___x_943_);
    return v___x_944_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHourMinuteSeconds(
    mut v_hour_945_: *mut LeanObject,
    mut v_minute_946_: *mut LeanObject,
    mut v_second_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    v___x_948_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once),
        _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0,
    );
    v___x_949_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_949_, 0, v_hour_945_);
    lean_ctor_set(v___x_949_, 1, v_minute_946_);
    lean_ctor_set(v___x_949_, 2, v_second_947_);
    lean_ctor_set(v___x_949_, 3, v___x_948_);
    return v___x_949_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(
    mut v_a_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    v___x_951_ = l_Rat_ofInt(v_a_950_);
    return v___x_951_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    v___x_952_ = lean_unsigned_to_nat(3600000);
    v___x_953_ = lean_nat_to_int(v___x_952_);
    return v___x_953_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__1() -> *mut LeanObject {
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    v___x_954_ = lean_unsigned_to_nat(60000);
    v___x_955_ = lean_nat_to_int(v___x_954_);
    return v___x_955_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__2() -> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v___x_956_ = lean_unsigned_to_nat(1000);
    v___x_957_ = lean_nat_to_int(v___x_956_);
    return v___x_957_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toMilliseconds___closed__3() -> *mut LeanObject {
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    v___x_958_ = lean_unsigned_to_nat(1000000);
    v___x_959_ = lean_nat_to_int(v___x_958_);
    return v___x_959_;
}
pub unsafe fn l_Std_Time_PlainTime_toMilliseconds(
    mut v_time_960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    v_hour_961_ = lean_ctor_get(v_time_960_, 0);
    v_minute_962_ = lean_ctor_get(v_time_960_, 1);
    v_second_963_ = lean_ctor_get(v_time_960_, 2);
    v_nanosecond_964_ = lean_ctor_get(v_time_960_, 3);
    v___x_965_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__0,
    );
    v___x_966_ = lean_int_mul(v_hour_961_, v___x_965_);
    v___x_967_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__1,
    );
    v___x_968_ = lean_int_mul(v_minute_962_, v___x_967_);
    v___x_969_ = lean_int_add(v___x_966_, v___x_968_);
    lean_dec(v___x_968_);
    lean_dec(v___x_966_);
    v___x_970_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__2,
    );
    v___x_971_ = lean_int_mul(v_second_963_, v___x_970_);
    v___x_972_ = lean_int_add(v___x_969_, v___x_971_);
    lean_dec(v___x_971_);
    lean_dec(v___x_969_);
    v___x_973_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_974_ = lean_int_div(v_nanosecond_964_, v___x_973_);
    v___x_975_ = lean_int_add(v___x_972_, v___x_974_);
    lean_dec(v___x_974_);
    lean_dec(v___x_972_);
    return v___x_975_;
}
pub unsafe fn l_Std_Time_PlainTime_toMilliseconds___boxed(
    mut v_time_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_977_: *mut LeanObject = core::ptr::null_mut();
    v_res_977_ = l_Std_Time_PlainTime_toMilliseconds(v_time_976_);
    lean_dec_ref(v_time_976_);
    return v_res_977_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(
    mut v_a_978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    v___x_979_ = lean_nat_to_int(v_a_978_);
    v___x_980_ = l_Rat_ofInt(v___x_979_);
    return v___x_980_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toNanoseconds___closed__0() -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_982_ = lean_nat_to_int(v___x_981_);
    return v___x_982_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toNanoseconds___closed__1() -> *mut LeanObject {
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    v___x_983_ = lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_984_ = lean_nat_to_int(v___x_983_);
    return v___x_984_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toNanoseconds___closed__2() -> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ = lean_unsigned_to_nat(1000000000);
    v___x_986_ = lean_nat_to_int(v___x_985_);
    return v___x_986_;
}
pub unsafe fn l_Std_Time_PlainTime_toNanoseconds(
    mut v_time_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    v_hour_988_ = lean_ctor_get(v_time_987_, 0);
    v_minute_989_ = lean_ctor_get(v_time_987_, 1);
    v_second_990_ = lean_ctor_get(v_time_987_, 2);
    v_nanosecond_991_ = lean_ctor_get(v_time_987_, 3);
    v___x_992_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_993_ = lean_int_mul(v_hour_988_, v___x_992_);
    v___x_994_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_995_ = lean_int_mul(v_minute_989_, v___x_994_);
    v___x_996_ = lean_int_add(v___x_993_, v___x_995_);
    lean_dec(v___x_995_);
    lean_dec(v___x_993_);
    v___x_997_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_998_ = lean_int_mul(v_second_990_, v___x_997_);
    v___x_999_ = lean_int_add(v___x_996_, v___x_998_);
    lean_dec(v___x_998_);
    lean_dec(v___x_996_);
    v___x_1000_ = lean_int_add(v___x_999_, v_nanosecond_991_);
    lean_dec(v___x_999_);
    return v___x_1000_;
}
pub unsafe fn l_Std_Time_PlainTime_toNanoseconds___boxed(
    mut v_time_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1002_: *mut LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1001_);
    lean_dec_ref(v_time_1001_);
    return v_res_1002_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toSeconds___closed__0() -> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = lean_unsigned_to_nat(3600);
    v___x_1004_ = lean_nat_to_int(v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_toSeconds___closed__1() -> *mut LeanObject {
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1005_ = lean_unsigned_to_nat(60);
    v___x_1006_ = lean_nat_to_int(v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Std_Time_PlainTime_toSeconds(mut v_time_1007_: *mut LeanObject) -> *mut LeanObject {
    let mut v_hour_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v_hour_1008_ = lean_ctor_get(v_time_1007_, 0);
    v_minute_1009_ = lean_ctor_get(v_time_1007_, 1);
    v_second_1010_ = lean_ctor_get(v_time_1007_, 2);
    v___x_1011_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__0,
    );
    v___x_1012_ = lean_int_mul(v_hour_1008_, v___x_1011_);
    v___x_1013_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__1,
    );
    v___x_1014_ = lean_int_mul(v_minute_1009_, v___x_1013_);
    v___x_1015_ = lean_int_add(v___x_1012_, v___x_1014_);
    lean_dec(v___x_1014_);
    lean_dec(v___x_1012_);
    v___x_1016_ = lean_int_add(v___x_1015_, v_second_1010_);
    lean_dec(v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Time_PlainTime_toSeconds___boxed(
    mut v_time_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_Time_PlainTime_toSeconds(v_time_1017_);
    lean_dec_ref(v_time_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Std_Time_PlainTime_toMinutes(mut v_time_1019_: *mut LeanObject) -> *mut LeanObject {
    let mut v_hour_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v_hour_1020_ = lean_ctor_get(v_time_1019_, 0);
    v_minute_1021_ = lean_ctor_get(v_time_1019_, 1);
    v_second_1022_ = lean_ctor_get(v_time_1019_, 2);
    v___x_1023_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__1,
    );
    v___x_1024_ = lean_int_mul(v_hour_1020_, v___x_1023_);
    v___x_1025_ = lean_int_add(v___x_1024_, v_minute_1021_);
    lean_dec(v___x_1024_);
    v___x_1026_ = lean_int_div(v_second_1022_, v___x_1023_);
    v___x_1027_ = lean_int_add(v___x_1025_, v___x_1026_);
    lean_dec(v___x_1026_);
    lean_dec(v___x_1025_);
    return v___x_1027_;
}
pub unsafe fn l_Std_Time_PlainTime_toMinutes___boxed(
    mut v_time_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Std_Time_PlainTime_toMinutes(v_time_1028_);
    lean_dec_ref(v_time_1028_);
    return v_res_1029_;
}
pub unsafe fn l_Std_Time_PlainTime_toHours(mut v_time_1030_: *mut LeanObject) -> *mut LeanObject {
    let mut v_hour_1031_: *mut LeanObject = core::ptr::null_mut();
    v_hour_1031_ = lean_ctor_get(v_time_1030_, 0);
    lean_inc(v_hour_1031_);
    return v_hour_1031_;
}
pub unsafe fn l_Std_Time_PlainTime_toHours___boxed(
    mut v_time_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1033_: *mut LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Std_Time_PlainTime_toHours(v_time_1032_);
    lean_dec_ref(v_time_1032_);
    return v_res_1033_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0() -> *mut LeanObject {
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    v___x_1034_ = lean_unsigned_to_nat(24);
    v___x_1035_ = lean_nat_to_int(v___x_1034_);
    return v___x_1035_;
}
pub unsafe fn l_Std_Time_PlainTime_ofNanoseconds(
    mut v_nanos_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remainingNanos_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hours_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minutes_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seconds_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    v___x_1037_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1038_ = lean_int_ediv(v_nanos_1036_, v___x_1037_);
    v_remainingNanos_1039_ = lean_int_emod(v_nanos_1036_, v___x_1037_);
    v___x_1040_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__0,
    );
    v___x_1041_ = lean_int_ediv(v___x_1038_, v___x_1040_);
    v___x_1042_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0,
    );
    v_hours_1043_ = lean_int_emod(v___x_1041_, v___x_1042_);
    lean_dec(v___x_1041_);
    v___x_1044_ = lean_int_emod(v___x_1038_, v___x_1040_);
    v___x_1045_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toSeconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toSeconds___closed__1,
    );
    v_minutes_1046_ = lean_int_ediv(v___x_1044_, v___x_1045_);
    lean_dec(v___x_1044_);
    v_seconds_1047_ = lean_int_emod(v___x_1038_, v___x_1045_);
    lean_dec(v___x_1038_);
    v___x_1048_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1048_, 0, v_hours_1043_);
    lean_ctor_set(v___x_1048_, 1, v_minutes_1046_);
    lean_ctor_set(v___x_1048_, 2, v_seconds_1047_);
    lean_ctor_set(v___x_1048_, 3, v_remainingNanos_1039_);
    return v___x_1048_;
}
pub unsafe fn l_Std_Time_PlainTime_ofNanoseconds___boxed(
    mut v_nanos_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_1049_);
    lean_dec(v_nanos_1049_);
    return v_res_1050_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMilliseconds(
    mut v_millis_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_1053_ = lean_int_mul(v_millis_1051_, v___x_1052_);
    v___x_1054_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1053_);
    lean_dec(v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMilliseconds___boxed(
    mut v_millis_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Std_Time_PlainTime_ofMilliseconds(v_millis_1055_);
    lean_dec(v_millis_1055_);
    return v_res_1056_;
}
pub unsafe fn l_Std_Time_PlainTime_ofSeconds(mut v_secs_1057_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    v___x_1058_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1059_ = lean_int_mul(v_secs_1057_, v___x_1058_);
    v___x_1060_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1059_);
    lean_dec(v___x_1059_);
    return v___x_1060_;
}
pub unsafe fn l_Std_Time_PlainTime_ofSeconds___boxed(
    mut v_secs_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Std_Time_PlainTime_ofSeconds(v_secs_1061_);
    lean_dec(v_secs_1061_);
    return v_res_1062_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMinutes(mut v_secs_1063_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    v___x_1064_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_1065_ = lean_int_mul(v_secs_1063_, v___x_1064_);
    v___x_1066_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1065_);
    lean_dec(v___x_1065_);
    return v___x_1066_;
}
pub unsafe fn l_Std_Time_PlainTime_ofMinutes___boxed(
    mut v_secs_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Std_Time_PlainTime_ofMinutes(v_secs_1067_);
    lean_dec(v_secs_1067_);
    return v_res_1068_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHours(mut v_hour_1069_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_1071_ = lean_int_mul(v_hour_1069_, v___x_1070_);
    v___x_1072_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1071_);
    lean_dec(v___x_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Std_Time_PlainTime_ofHours___boxed(
    mut v_hour_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Std_Time_PlainTime_ofHours(v_hour_1073_);
    lean_dec(v_hour_1073_);
    return v_res_1074_;
}
pub unsafe fn l_Std_Time_PlainTime_addSeconds(
    mut v_time_1075_: *mut LeanObject,
    mut v_secondsToAdd_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_totalSeconds_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1077_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1075_);
    v___x_1078_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1079_ = lean_int_mul(v_secondsToAdd_1076_, v___x_1078_);
    v_totalSeconds_1080_ = lean_int_add(v___x_1077_, v___x_1079_);
    lean_dec(v___x_1079_);
    lean_dec(v___x_1077_);
    v___x_1081_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_1080_);
    lean_dec(v_totalSeconds_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Std_Time_PlainTime_addSeconds___boxed(
    mut v_time_1082_: *mut LeanObject,
    mut v_secondsToAdd_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1084_: *mut LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Std_Time_PlainTime_addSeconds(v_time_1082_, v_secondsToAdd_1083_);
    lean_dec(v_secondsToAdd_1083_);
    lean_dec_ref(v_time_1082_);
    return v_res_1084_;
}
pub unsafe fn l_Std_Time_PlainTime_subSeconds(
    mut v_time_1085_: *mut LeanObject,
    mut v_secondsToSub_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_totalSeconds_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = lean_int_neg(v_secondsToSub_1086_);
    v___x_1088_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1085_);
    v___x_1089_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__2_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__2,
    );
    v___x_1090_ = lean_int_mul(v___x_1087_, v___x_1089_);
    lean_dec(v___x_1087_);
    v_totalSeconds_1091_ = lean_int_add(v___x_1088_, v___x_1090_);
    lean_dec(v___x_1090_);
    lean_dec(v___x_1088_);
    v___x_1092_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_1091_);
    lean_dec(v_totalSeconds_1091_);
    return v___x_1092_;
}
pub unsafe fn l_Std_Time_PlainTime_subSeconds___boxed(
    mut v_time_1093_: *mut LeanObject,
    mut v_secondsToSub_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1095_: *mut LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Std_Time_PlainTime_subSeconds(v_time_1093_, v_secondsToSub_1094_);
    lean_dec(v_secondsToSub_1094_);
    lean_dec_ref(v_time_1093_);
    return v_res_1095_;
}
pub unsafe fn l_Std_Time_PlainTime_addMinutes(
    mut v_time_1096_: *mut LeanObject,
    mut v_minutesToAdd_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_total_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1098_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1096_);
    v___x_1099_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_1100_ = lean_int_mul(v_minutesToAdd_1097_, v___x_1099_);
    v_total_1101_ = lean_int_add(v___x_1098_, v___x_1100_);
    lean_dec(v___x_1100_);
    lean_dec(v___x_1098_);
    v___x_1102_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1101_);
    lean_dec(v_total_1101_);
    return v___x_1102_;
}
pub unsafe fn l_Std_Time_PlainTime_addMinutes___boxed(
    mut v_time_1103_: *mut LeanObject,
    mut v_minutesToAdd_1104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1105_: *mut LeanObject = core::ptr::null_mut();
    v_res_1105_ = l_Std_Time_PlainTime_addMinutes(v_time_1103_, v_minutesToAdd_1104_);
    lean_dec(v_minutesToAdd_1104_);
    lean_dec_ref(v_time_1103_);
    return v_res_1105_;
}
pub unsafe fn l_Std_Time_PlainTime_subMinutes(
    mut v_time_1106_: *mut LeanObject,
    mut v_minutesToSub_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_total_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v___x_1108_ = lean_int_neg(v_minutesToSub_1107_);
    v___x_1109_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1106_);
    v___x_1110_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__1_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__1,
    );
    v___x_1111_ = lean_int_mul(v___x_1108_, v___x_1110_);
    lean_dec(v___x_1108_);
    v_total_1112_ = lean_int_add(v___x_1109_, v___x_1111_);
    lean_dec(v___x_1111_);
    lean_dec(v___x_1109_);
    v___x_1113_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1112_);
    lean_dec(v_total_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_Time_PlainTime_subMinutes___boxed(
    mut v_time_1114_: *mut LeanObject,
    mut v_minutesToSub_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1116_: *mut LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Std_Time_PlainTime_subMinutes(v_time_1114_, v_minutesToSub_1115_);
    lean_dec(v_minutesToSub_1115_);
    lean_dec_ref(v_time_1114_);
    return v_res_1116_;
}
pub unsafe fn l_Std_Time_PlainTime_addHours(
    mut v_time_1117_: *mut LeanObject,
    mut v_hoursToAdd_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_total_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1119_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1117_);
    v___x_1120_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_1121_ = lean_int_mul(v_hoursToAdd_1118_, v___x_1120_);
    v_total_1122_ = lean_int_add(v___x_1119_, v___x_1121_);
    lean_dec(v___x_1121_);
    lean_dec(v___x_1119_);
    v___x_1123_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1122_);
    lean_dec(v_total_1122_);
    return v___x_1123_;
}
pub unsafe fn l_Std_Time_PlainTime_addHours___boxed(
    mut v_time_1124_: *mut LeanObject,
    mut v_hoursToAdd_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1126_: *mut LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Std_Time_PlainTime_addHours(v_time_1124_, v_hoursToAdd_1125_);
    lean_dec(v_hoursToAdd_1125_);
    lean_dec_ref(v_time_1124_);
    return v_res_1126_;
}
pub unsafe fn l_Std_Time_PlainTime_subHours(
    mut v_time_1127_: *mut LeanObject,
    mut v_hoursToSub_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_total_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = lean_int_neg(v_hoursToSub_1128_);
    v___x_1130_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1127_);
    v___x_1131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toNanoseconds___closed__0_once),
        _init_l_Std_Time_PlainTime_toNanoseconds___closed__0,
    );
    v___x_1132_ = lean_int_mul(v___x_1129_, v___x_1131_);
    lean_dec(v___x_1129_);
    v_total_1133_ = lean_int_add(v___x_1130_, v___x_1132_);
    lean_dec(v___x_1132_);
    lean_dec(v___x_1130_);
    v___x_1134_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1133_);
    lean_dec(v_total_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Std_Time_PlainTime_subHours___boxed(
    mut v_time_1135_: *mut LeanObject,
    mut v_hoursToSub_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Std_Time_PlainTime_subHours(v_time_1135_, v_hoursToSub_1136_);
    lean_dec(v_hoursToSub_1136_);
    lean_dec_ref(v_time_1135_);
    return v_res_1137_;
}
pub unsafe fn l_Std_Time_PlainTime_addNanoseconds(
    mut v_time_1138_: *mut LeanObject,
    mut v_nanosToAdd_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_total_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1140_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1138_);
    v_total_1141_ = lean_int_add(v___x_1140_, v_nanosToAdd_1139_);
    lean_dec(v___x_1140_);
    v___x_1142_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_1141_);
    lean_dec(v_total_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Std_Time_PlainTime_addNanoseconds___boxed(
    mut v_time_1143_: *mut LeanObject,
    mut v_nanosToAdd_1144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1145_: *mut LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Std_Time_PlainTime_addNanoseconds(v_time_1143_, v_nanosToAdd_1144_);
    lean_dec(v_nanosToAdd_1144_);
    lean_dec_ref(v_time_1143_);
    return v_res_1145_;
}
pub unsafe fn l_Std_Time_PlainTime_subNanoseconds(
    mut v_time_1146_: *mut LeanObject,
    mut v_nanosToSub_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    v___x_1148_ = lean_int_neg(v_nanosToSub_1147_);
    v___x_1149_ = l_Std_Time_PlainTime_addNanoseconds(v_time_1146_, v___x_1148_);
    lean_dec(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn l_Std_Time_PlainTime_subNanoseconds___boxed(
    mut v_time_1150_: *mut LeanObject,
    mut v_nanosToSub_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1152_: *mut LeanObject = core::ptr::null_mut();
    v_res_1152_ = l_Std_Time_PlainTime_subNanoseconds(v_time_1150_, v_nanosToSub_1151_);
    lean_dec(v_nanosToSub_1151_);
    lean_dec_ref(v_time_1150_);
    return v_res_1152_;
}
pub unsafe fn l_Std_Time_PlainTime_addMilliseconds(
    mut v_time_1153_: *mut LeanObject,
    mut v_millisToAdd_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_total_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    v___x_1155_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1153_);
    v_total_1156_ = lean_int_add(v___x_1155_, v_millisToAdd_1154_);
    lean_dec(v___x_1155_);
    v___x_1157_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_1158_ = lean_int_mul(v_total_1156_, v___x_1157_);
    lean_dec(v_total_1156_);
    v___x_1159_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1158_);
    lean_dec(v___x_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_Time_PlainTime_addMilliseconds___boxed(
    mut v_time_1160_: *mut LeanObject,
    mut v_millisToAdd_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1162_: *mut LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_Time_PlainTime_addMilliseconds(v_time_1160_, v_millisToAdd_1161_);
    lean_dec(v_millisToAdd_1161_);
    lean_dec_ref(v_time_1160_);
    return v_res_1162_;
}
pub unsafe fn l_Std_Time_PlainTime_subMilliseconds(
    mut v_time_1163_: *mut LeanObject,
    mut v_millisToSub_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1165_ = lean_int_neg(v_millisToSub_1164_);
    v___x_1166_ = l_Std_Time_PlainTime_addMilliseconds(v_time_1163_, v___x_1165_);
    lean_dec(v___x_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_Time_PlainTime_subMilliseconds___boxed(
    mut v_time_1167_: *mut LeanObject,
    mut v_millisToSub_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1169_: *mut LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Std_Time_PlainTime_subMilliseconds(v_time_1167_, v_millisToSub_1168_);
    lean_dec(v_millisToSub_1168_);
    lean_dec_ref(v_time_1167_);
    return v_res_1169_;
}
pub unsafe fn l_Std_Time_PlainTime_withSeconds(
    mut v_pt_1170_: *mut LeanObject,
    mut v_second_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_unused_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1172_ = lean_ctor_get(v_pt_1170_, 0);
                v_minute_1173_ = lean_ctor_get(v_pt_1170_, 1);
                v_nanosecond_1174_ = lean_ctor_get(v_pt_1170_, 3);
                v_isSharedCheck_1181_ = (!lean_is_exclusive(v_pt_1170_)) as u8;
                if v_isSharedCheck_1181_ == 0 {
                    v_unused_1182_ = lean_ctor_get(v_pt_1170_, 2);
                    lean_dec(v_unused_1182_);
                    v___x_1176_ = v_pt_1170_;
                    v_isShared_1177_ = v_isSharedCheck_1181_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nanosecond_1174_);
                    lean_inc(v_minute_1173_);
                    lean_inc(v_hour_1172_);
                    lean_dec(v_pt_1170_);
                    v___x_1176_ = lean_box(0);
                    v_isShared_1177_ = v_isSharedCheck_1181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1177_ == 0 {
                    lean_ctor_set(v___x_1176_, 2, v_second_1171_);
                    v___x_1179_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_hour_1172_);
                    lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_minute_1173_);
                    lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_second_1171_);
                    lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_nanosecond_1174_);
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
    mut v_pt_1183_: *mut LeanObject,
    mut v_minute_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut v_unused_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1185_ = lean_ctor_get(v_pt_1183_, 0);
                v_second_1186_ = lean_ctor_get(v_pt_1183_, 2);
                v_nanosecond_1187_ = lean_ctor_get(v_pt_1183_, 3);
                v_isSharedCheck_1194_ = (!lean_is_exclusive(v_pt_1183_)) as u8;
                if v_isSharedCheck_1194_ == 0 {
                    v_unused_1195_ = lean_ctor_get(v_pt_1183_, 1);
                    lean_dec(v_unused_1195_);
                    v___x_1189_ = v_pt_1183_;
                    v_isShared_1190_ = v_isSharedCheck_1194_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nanosecond_1187_);
                    lean_inc(v_second_1186_);
                    lean_inc(v_hour_1185_);
                    lean_dec(v_pt_1183_);
                    v___x_1189_ = lean_box(0);
                    v_isShared_1190_ = v_isSharedCheck_1194_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1190_ == 0 {
                    lean_ctor_set(v___x_1189_, 1, v_minute_1184_);
                    v___x_1192_ = v___x_1189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_hour_1185_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_minute_1184_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_second_1186_);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_nanosecond_1187_);
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
    mut v_pt_1196_: *mut LeanObject,
    mut v_millis_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1204_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1198_ = lean_ctor_get(v_pt_1196_, 0);
                v_minute_1199_ = lean_ctor_get(v_pt_1196_, 1);
                v_second_1200_ = lean_ctor_get(v_pt_1196_, 2);
                v_nanosecond_1201_ = lean_ctor_get(v_pt_1196_, 3);
                v_isSharedCheck_1213_ = (!lean_is_exclusive(v_pt_1196_)) as u8;
                if v_isSharedCheck_1213_ == 0 {
                    v___x_1203_ = v_pt_1196_;
                    v_isShared_1204_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nanosecond_1201_);
                    lean_inc(v_second_1200_);
                    lean_inc(v_minute_1199_);
                    lean_inc(v_hour_1198_);
                    lean_dec(v_pt_1196_);
                    v___x_1203_ = lean_box(0);
                    v_isShared_1204_ = v_isSharedCheck_1213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1205_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__2_once),
                    _init_l_Std_Time_PlainTime_toMilliseconds___closed__2,
                );
                v___x_1206_ = lean_int_emod(v_nanosecond_1201_, v___x_1205_);
                lean_dec(v_nanosecond_1201_);
                v___x_1207_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
                    _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
                );
                v___x_1208_ = lean_int_mul(v_millis_1197_, v___x_1207_);
                v___x_1209_ = lean_int_add(v___x_1208_, v___x_1206_);
                lean_dec(v___x_1206_);
                lean_dec(v___x_1208_);
                if v_isShared_1204_ == 0 {
                    lean_ctor_set(v___x_1203_, 3, v___x_1209_);
                    v___x_1211_ = v___x_1203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_hour_1198_);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_minute_1199_);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_second_1200_);
                    lean_ctor_set(v_reuseFailAlloc_1212_, 3, v___x_1209_);
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
    mut v_pt_1214_: *mut LeanObject,
    mut v_millis_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1216_: *mut LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Std_Time_PlainTime_withMilliseconds(v_pt_1214_, v_millis_1215_);
    lean_dec(v_millis_1215_);
    return v_res_1216_;
}
pub unsafe fn l_Std_Time_PlainTime_withNanoseconds(
    mut v_pt_1217_: *mut LeanObject,
    mut v_nano_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hour_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_unused_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hour_1219_ = lean_ctor_get(v_pt_1217_, 0);
                v_minute_1220_ = lean_ctor_get(v_pt_1217_, 1);
                v_second_1221_ = lean_ctor_get(v_pt_1217_, 2);
                v_isSharedCheck_1228_ = (!lean_is_exclusive(v_pt_1217_)) as u8;
                if v_isSharedCheck_1228_ == 0 {
                    v_unused_1229_ = lean_ctor_get(v_pt_1217_, 3);
                    lean_dec(v_unused_1229_);
                    v___x_1223_ = v_pt_1217_;
                    v_isShared_1224_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_second_1221_);
                    lean_inc(v_minute_1220_);
                    lean_inc(v_hour_1219_);
                    lean_dec(v_pt_1217_);
                    v___x_1223_ = lean_box(0);
                    v_isShared_1224_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1224_ == 0 {
                    lean_ctor_set(v___x_1223_, 3, v_nano_1218_);
                    v___x_1226_ = v___x_1223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_hour_1219_);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_minute_1220_);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_second_1221_);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_nano_1218_);
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
    mut v_pt_1230_: *mut LeanObject,
    mut v_hour_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minute_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut v_unused_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_minute_1232_ = lean_ctor_get(v_pt_1230_, 1);
                v_second_1233_ = lean_ctor_get(v_pt_1230_, 2);
                v_nanosecond_1234_ = lean_ctor_get(v_pt_1230_, 3);
                v_isSharedCheck_1241_ = (!lean_is_exclusive(v_pt_1230_)) as u8;
                if v_isSharedCheck_1241_ == 0 {
                    v_unused_1242_ = lean_ctor_get(v_pt_1230_, 0);
                    lean_dec(v_unused_1242_);
                    v___x_1236_ = v_pt_1230_;
                    v_isShared_1237_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nanosecond_1234_);
                    lean_inc(v_second_1233_);
                    lean_inc(v_minute_1232_);
                    lean_dec(v_pt_1230_);
                    v___x_1236_ = lean_box(0);
                    v_isShared_1237_ = v_isSharedCheck_1241_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1237_ == 0 {
                    lean_ctor_set(v___x_1236_, 0, v_hour_1231_);
                    v___x_1239_ = v___x_1236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_hour_1231_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_minute_1232_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_second_1233_);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_nanosecond_1234_);
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
pub unsafe fn l_Std_Time_PlainTime_millisecond(mut v_pt_1243_: *mut LeanObject) -> *mut LeanObject {
    let mut v_nanosecond_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    v_nanosecond_1244_ = lean_ctor_get(v_pt_1243_, 3);
    v___x_1245_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_toMilliseconds___closed__3_once),
        _init_l_Std_Time_PlainTime_toMilliseconds___closed__3,
    );
    v___x_1246_ = lean_int_ediv(v_nanosecond_1244_, v___x_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Std_Time_PlainTime_millisecond___boxed(
    mut v_pt_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1248_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Std_Time_PlainTime_millisecond(v_pt_1247_);
    lean_dec_ref(v_pt_1247_);
    return v_res_1248_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_PlainTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_instInhabitedPlainTime = _init_l_Std_Time_instInhabitedPlainTime();
    lean_mark_persistent(l_Std_Time_instInhabitedPlainTime);
    l_Std_Time_PlainTime_midnight = _init_l_Std_Time_PlainTime_midnight();
    lean_mark_persistent(l_Std_Time_PlainTime_midnight);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_PlainTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_PlainTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_PlainTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_PlainTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Time_PlainTime(builtin);
}
