// Lean compiler output
// Module: Std.Time.Date.Unit.Weekday
// Imports: Std.Time.Date.Unit.Day
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::l_compareOn___boxed;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Time::Date::Unit::Day::{
    initialize_Std_Time_Date_Unit_Day, runtime_initialize_Std_Time_Date_Unit_Day,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_sub, lean_nat_abs,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_emod;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Time_instReprWeekday_repr___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 109, 111,
            110, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__2_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 116, 117,
            101, 115, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__4_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 119, 101,
            100, 110, 101, 115, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__5_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__6_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 116, 104,
            117, 114, 115, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__6_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__7_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__8_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 102, 114,
            105, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__8_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__9_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__10_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 115, 97,
            116, 117, 114, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__10_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__11_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__11_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__12_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 115, 117,
            110, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_instReprWeekday_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__12_value) as *mut LeanObject;
pub static l_Std_Time_instReprWeekday_repr___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_instReprWeekday_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday_repr___closed__13_value) as *mut LeanObject;
static mut l_Std_Time_instReprWeekday_repr___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprWeekday_repr___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instReprWeekday_repr___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprWeekday_repr___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instReprWeekday___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_instReprWeekday_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instReprWeekday___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instReprWeekday: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWeekday___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instInhabitedWeekday_default: u8 = 0;
pub static mut l_Std_Time_instInhabitedWeekday: u8 = 0;
static mut l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Weekday_instReprOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Weekday_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Weekday_instReprOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Weekday_instReprOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Weekday_instLTOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Weekday_instLEOrdinal: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_instInhabitedOrdinal___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Weekday_instInhabitedOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Weekday_instOrdOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Weekday_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Weekday_instOrdOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Weekday_instOrdOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instOrdOrdinal___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Weekday_toOrdinal___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__26: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__27: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__31: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__32: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__33: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__34: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__35_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__35: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__36_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__36: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__37_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__37: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__38: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__39_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__39: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__40_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__40: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Weekday_toOrdinal___closed__41_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_toOrdinal___closed__41: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Weekday_instOrd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_Weekday_toOrdinal___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Weekday_instOrd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instOrd___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_instOrd___closed__1_value: LeanClosureObject<4> = LeanClosureObject {
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
        core::ptr::addr_of!(l_Std_Time_Weekday_instOrdOrdinal___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_Weekday_instOrd___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Std_Time_Weekday_instOrd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instOrd___closed__1_value) as *mut LeanObject;
pub static mut l_Std_Time_Weekday_instOrd: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_instOrd___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((6 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((5 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__2_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((4 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__5_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x3f___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Time_Weekday_ofNat_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x3f___closed__6_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x21___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 68, 97, 116, 101, 46, 85, 110, 105, 116, 46,
            87, 101, 101, 107, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_Weekday_ofNat_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x21___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x21___closed__1_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 87, 101, 101, 107, 100, 97, 121, 46, 111, 102,
            78, 97, 116, 33, 0,
        ],
    };
static mut l_Std_Time_Weekday_ofNat_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x21___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Weekday_ofNat_x21___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 119, 101, 101, 107, 100, 97, 121, 0,
        ],
    };
static mut l_Std_Time_Weekday_ofNat_x21___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Weekday_ofNat_x21___closed__2_value) as *mut LeanObject;
static mut l_Std_Time_Weekday_ofNat_x21___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Weekday_ofNat_x21___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Time_Weekday_ctorIdx(mut v_x_732_: u8) -> *mut LeanObject {
    match v_x_732_ {
        0 => {
            let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
            v___x_733_ = lean_unsigned_to_nat(0);
            return v___x_733_;
        }
        1 => {
            let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
            v___x_734_ = lean_unsigned_to_nat(1);
            return v___x_734_;
        }
        2 => {
            let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
            v___x_735_ = lean_unsigned_to_nat(2);
            return v___x_735_;
        }
        3 => {
            let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
            v___x_736_ = lean_unsigned_to_nat(3);
            return v___x_736_;
        }
        4 => {
            let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
            v___x_737_ = lean_unsigned_to_nat(4);
            return v___x_737_;
        }
        5 => {
            let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
            v___x_738_ = lean_unsigned_to_nat(5);
            return v___x_738_;
        }
        _ => {
            let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
            v___x_739_ = lean_unsigned_to_nat(6);
            return v___x_739_;
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_ctorIdx___boxed(mut v_x_740_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_741_: u8 = 0;
    let mut v_res_742_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_741_ = (lean_unbox(v_x_740_) as u8);
    v_res_742_ = l_Std_Time_Weekday_ctorIdx(v_x_boxed_741_);
    return v_res_742_;
}
pub unsafe fn l_Std_Time_Weekday_toCtorIdx(mut v_x_743_: u8) -> *mut LeanObject {
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Std_Time_Weekday_ctorIdx(v_x_743_);
    return v___x_744_;
}
pub unsafe fn l_Std_Time_Weekday_toCtorIdx___boxed(
    mut v_x_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_746_: u8 = 0;
    let mut v_res_747_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_746_ = (lean_unbox(v_x_745_) as u8);
    v_res_747_ = l_Std_Time_Weekday_toCtorIdx(v_x_4__boxed_746_);
    return v_res_747_;
}
pub unsafe fn l_Std_Time_Weekday_ctorElim___redArg(
    mut v_k_748_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_748_);
    return v_k_748_;
}
pub unsafe fn l_Std_Time_Weekday_ctorElim___redArg___boxed(
    mut v_k_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_750_: *mut LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Std_Time_Weekday_ctorElim___redArg(v_k_749_);
    lean_dec(v_k_749_);
    return v_res_750_;
}
pub unsafe fn l_Std_Time_Weekday_ctorElim(
    mut v_motive_751_: *mut LeanObject,
    mut v_ctorIdx_752_: *mut LeanObject,
    mut v_t_753_: u8,
    mut v_h_754_: *mut LeanObject,
    mut v_k_755_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_755_);
    return v_k_755_;
}
pub unsafe fn l_Std_Time_Weekday_ctorElim___boxed(
    mut v_motive_756_: *mut LeanObject,
    mut v_ctorIdx_757_: *mut LeanObject,
    mut v_t_758_: *mut LeanObject,
    mut v_h_759_: *mut LeanObject,
    mut v_k_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_761_: u8 = 0;
    let mut v_res_762_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_761_ = (lean_unbox(v_t_758_) as u8);
    v_res_762_ = l_Std_Time_Weekday_ctorElim(
        v_motive_756_,
        v_ctorIdx_757_,
        v_t_boxed_761_,
        v_h_759_,
        v_k_760_,
    );
    lean_dec(v_k_760_);
    lean_dec(v_ctorIdx_757_);
    return v_res_762_;
}
pub unsafe fn l_Std_Time_Weekday_monday_elim___redArg(
    mut v_monday_763_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_monday_763_);
    return v_monday_763_;
}
pub unsafe fn l_Std_Time_Weekday_monday_elim___redArg___boxed(
    mut v_monday_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_765_: *mut LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Std_Time_Weekday_monday_elim___redArg(v_monday_764_);
    lean_dec(v_monday_764_);
    return v_res_765_;
}
pub unsafe fn l_Std_Time_Weekday_monday_elim(
    mut v_motive_766_: *mut LeanObject,
    mut v_t_767_: u8,
    mut v_h_768_: *mut LeanObject,
    mut v_monday_769_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_monday_769_);
    return v_monday_769_;
}
pub unsafe fn l_Std_Time_Weekday_monday_elim___boxed(
    mut v_motive_770_: *mut LeanObject,
    mut v_t_771_: *mut LeanObject,
    mut v_h_772_: *mut LeanObject,
    mut v_monday_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_774_: u8 = 0;
    let mut v_res_775_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_774_ = (lean_unbox(v_t_771_) as u8);
    v_res_775_ =
        l_Std_Time_Weekday_monday_elim(v_motive_770_, v_t_boxed_774_, v_h_772_, v_monday_773_);
    lean_dec(v_monday_773_);
    return v_res_775_;
}
pub unsafe fn l_Std_Time_Weekday_tuesday_elim___redArg(
    mut v_tuesday_776_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_tuesday_776_);
    return v_tuesday_776_;
}
pub unsafe fn l_Std_Time_Weekday_tuesday_elim___redArg___boxed(
    mut v_tuesday_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Std_Time_Weekday_tuesday_elim___redArg(v_tuesday_777_);
    lean_dec(v_tuesday_777_);
    return v_res_778_;
}
pub unsafe fn l_Std_Time_Weekday_tuesday_elim(
    mut v_motive_779_: *mut LeanObject,
    mut v_t_780_: u8,
    mut v_h_781_: *mut LeanObject,
    mut v_tuesday_782_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_tuesday_782_);
    return v_tuesday_782_;
}
pub unsafe fn l_Std_Time_Weekday_tuesday_elim___boxed(
    mut v_motive_783_: *mut LeanObject,
    mut v_t_784_: *mut LeanObject,
    mut v_h_785_: *mut LeanObject,
    mut v_tuesday_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_787_: u8 = 0;
    let mut v_res_788_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_787_ = (lean_unbox(v_t_784_) as u8);
    v_res_788_ =
        l_Std_Time_Weekday_tuesday_elim(v_motive_783_, v_t_boxed_787_, v_h_785_, v_tuesday_786_);
    lean_dec(v_tuesday_786_);
    return v_res_788_;
}
pub unsafe fn l_Std_Time_Weekday_wednesday_elim___redArg(
    mut v_wednesday_789_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_wednesday_789_);
    return v_wednesday_789_;
}
pub unsafe fn l_Std_Time_Weekday_wednesday_elim___redArg___boxed(
    mut v_wednesday_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Std_Time_Weekday_wednesday_elim___redArg(v_wednesday_790_);
    lean_dec(v_wednesday_790_);
    return v_res_791_;
}
pub unsafe fn l_Std_Time_Weekday_wednesday_elim(
    mut v_motive_792_: *mut LeanObject,
    mut v_t_793_: u8,
    mut v_h_794_: *mut LeanObject,
    mut v_wednesday_795_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_wednesday_795_);
    return v_wednesday_795_;
}
pub unsafe fn l_Std_Time_Weekday_wednesday_elim___boxed(
    mut v_motive_796_: *mut LeanObject,
    mut v_t_797_: *mut LeanObject,
    mut v_h_798_: *mut LeanObject,
    mut v_wednesday_799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_800_: u8 = 0;
    let mut v_res_801_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_800_ = (lean_unbox(v_t_797_) as u8);
    v_res_801_ = l_Std_Time_Weekday_wednesday_elim(
        v_motive_796_,
        v_t_boxed_800_,
        v_h_798_,
        v_wednesday_799_,
    );
    lean_dec(v_wednesday_799_);
    return v_res_801_;
}
pub unsafe fn l_Std_Time_Weekday_thursday_elim___redArg(
    mut v_thursday_802_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_thursday_802_);
    return v_thursday_802_;
}
pub unsafe fn l_Std_Time_Weekday_thursday_elim___redArg___boxed(
    mut v_thursday_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_804_: *mut LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Std_Time_Weekday_thursday_elim___redArg(v_thursday_803_);
    lean_dec(v_thursday_803_);
    return v_res_804_;
}
pub unsafe fn l_Std_Time_Weekday_thursday_elim(
    mut v_motive_805_: *mut LeanObject,
    mut v_t_806_: u8,
    mut v_h_807_: *mut LeanObject,
    mut v_thursday_808_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_thursday_808_);
    return v_thursday_808_;
}
pub unsafe fn l_Std_Time_Weekday_thursday_elim___boxed(
    mut v_motive_809_: *mut LeanObject,
    mut v_t_810_: *mut LeanObject,
    mut v_h_811_: *mut LeanObject,
    mut v_thursday_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_813_: u8 = 0;
    let mut v_res_814_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_813_ = (lean_unbox(v_t_810_) as u8);
    v_res_814_ =
        l_Std_Time_Weekday_thursday_elim(v_motive_809_, v_t_boxed_813_, v_h_811_, v_thursday_812_);
    lean_dec(v_thursday_812_);
    return v_res_814_;
}
pub unsafe fn l_Std_Time_Weekday_friday_elim___redArg(
    mut v_friday_815_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_friday_815_);
    return v_friday_815_;
}
pub unsafe fn l_Std_Time_Weekday_friday_elim___redArg___boxed(
    mut v_friday_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_817_: *mut LeanObject = core::ptr::null_mut();
    v_res_817_ = l_Std_Time_Weekday_friday_elim___redArg(v_friday_816_);
    lean_dec(v_friday_816_);
    return v_res_817_;
}
pub unsafe fn l_Std_Time_Weekday_friday_elim(
    mut v_motive_818_: *mut LeanObject,
    mut v_t_819_: u8,
    mut v_h_820_: *mut LeanObject,
    mut v_friday_821_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_friday_821_);
    return v_friday_821_;
}
pub unsafe fn l_Std_Time_Weekday_friday_elim___boxed(
    mut v_motive_822_: *mut LeanObject,
    mut v_t_823_: *mut LeanObject,
    mut v_h_824_: *mut LeanObject,
    mut v_friday_825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_826_: u8 = 0;
    let mut v_res_827_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_826_ = (lean_unbox(v_t_823_) as u8);
    v_res_827_ =
        l_Std_Time_Weekday_friday_elim(v_motive_822_, v_t_boxed_826_, v_h_824_, v_friday_825_);
    lean_dec(v_friday_825_);
    return v_res_827_;
}
pub unsafe fn l_Std_Time_Weekday_saturday_elim___redArg(
    mut v_saturday_828_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_saturday_828_);
    return v_saturday_828_;
}
pub unsafe fn l_Std_Time_Weekday_saturday_elim___redArg___boxed(
    mut v_saturday_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Std_Time_Weekday_saturday_elim___redArg(v_saturday_829_);
    lean_dec(v_saturday_829_);
    return v_res_830_;
}
pub unsafe fn l_Std_Time_Weekday_saturday_elim(
    mut v_motive_831_: *mut LeanObject,
    mut v_t_832_: u8,
    mut v_h_833_: *mut LeanObject,
    mut v_saturday_834_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_saturday_834_);
    return v_saturday_834_;
}
pub unsafe fn l_Std_Time_Weekday_saturday_elim___boxed(
    mut v_motive_835_: *mut LeanObject,
    mut v_t_836_: *mut LeanObject,
    mut v_h_837_: *mut LeanObject,
    mut v_saturday_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_839_: u8 = 0;
    let mut v_res_840_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_839_ = (lean_unbox(v_t_836_) as u8);
    v_res_840_ =
        l_Std_Time_Weekday_saturday_elim(v_motive_835_, v_t_boxed_839_, v_h_837_, v_saturday_838_);
    lean_dec(v_saturday_838_);
    return v_res_840_;
}
pub unsafe fn l_Std_Time_Weekday_sunday_elim___redArg(
    mut v_sunday_841_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_sunday_841_);
    return v_sunday_841_;
}
pub unsafe fn l_Std_Time_Weekday_sunday_elim___redArg___boxed(
    mut v_sunday_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_843_: *mut LeanObject = core::ptr::null_mut();
    v_res_843_ = l_Std_Time_Weekday_sunday_elim___redArg(v_sunday_842_);
    lean_dec(v_sunday_842_);
    return v_res_843_;
}
pub unsafe fn l_Std_Time_Weekday_sunday_elim(
    mut v_motive_844_: *mut LeanObject,
    mut v_t_845_: u8,
    mut v_h_846_: *mut LeanObject,
    mut v_sunday_847_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_sunday_847_);
    return v_sunday_847_;
}
pub unsafe fn l_Std_Time_Weekday_sunday_elim___boxed(
    mut v_motive_848_: *mut LeanObject,
    mut v_t_849_: *mut LeanObject,
    mut v_h_850_: *mut LeanObject,
    mut v_sunday_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_852_: u8 = 0;
    let mut v_res_853_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_852_ = (lean_unbox(v_t_849_) as u8);
    v_res_853_ =
        l_Std_Time_Weekday_sunday_elim(v_motive_848_, v_t_boxed_852_, v_h_850_, v_sunday_851_);
    lean_dec(v_sunday_851_);
    return v_res_853_;
}
pub unsafe fn _init_l_Std_Time_instReprWeekday_repr___closed__14() -> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = lean_unsigned_to_nat(2);
    v___x_876_ = lean_nat_to_int(v___x_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_Std_Time_instReprWeekday_repr___closed__15() -> *mut LeanObject {
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = lean_unsigned_to_nat(1);
    v___x_878_ = lean_nat_to_int(v___x_877_);
    return v___x_878_;
}
pub unsafe fn l_Std_Time_instReprWeekday_repr(
    mut v_x_879_: u8,
    mut v_prec_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: u8 = 0;
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: u8 = 0;
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: u8 = 0;
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: u8 = 0;
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: u8 = 0;
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_879_ {
                0 => {
                    v___x_930_ = lean_unsigned_to_nat(1024);
                    v___x_931_ = lean_nat_dec_le(v___x_930_, v_prec_880_);
                    if v___x_931_ == 0 {
                        v___x_932_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_882_ = v___x_932_;
                        state = 1;
                        continue;
                    } else {
                        v___x_933_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_882_ = v___x_933_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_934_ = lean_unsigned_to_nat(1024);
                    v___x_935_ = lean_nat_dec_le(v___x_934_, v_prec_880_);
                    if v___x_935_ == 0 {
                        v___x_936_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_889_ = v___x_936_;
                        state = 2;
                        continue;
                    } else {
                        v___x_937_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_889_ = v___x_937_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_938_ = lean_unsigned_to_nat(1024);
                    v___x_939_ = lean_nat_dec_le(v___x_938_, v_prec_880_);
                    if v___x_939_ == 0 {
                        v___x_940_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_896_ = v___x_940_;
                        state = 3;
                        continue;
                    } else {
                        v___x_941_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_896_ = v___x_941_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_942_ = lean_unsigned_to_nat(1024);
                    v___x_943_ = lean_nat_dec_le(v___x_942_, v_prec_880_);
                    if v___x_943_ == 0 {
                        v___x_944_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_903_ = v___x_944_;
                        state = 4;
                        continue;
                    } else {
                        v___x_945_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_903_ = v___x_945_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_946_ = lean_unsigned_to_nat(1024);
                    v___x_947_ = lean_nat_dec_le(v___x_946_, v_prec_880_);
                    if v___x_947_ == 0 {
                        v___x_948_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_910_ = v___x_948_;
                        state = 5;
                        continue;
                    } else {
                        v___x_949_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_910_ = v___x_949_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v___x_950_ = lean_unsigned_to_nat(1024);
                    v___x_951_ = lean_nat_dec_le(v___x_950_, v_prec_880_);
                    if v___x_951_ == 0 {
                        v___x_952_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_917_ = v___x_952_;
                        state = 6;
                        continue;
                    } else {
                        v___x_953_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_917_ = v___x_953_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    v___x_954_ = lean_unsigned_to_nat(1024);
                    v___x_955_ = lean_nat_dec_le(v___x_954_, v_prec_880_);
                    if v___x_955_ == 0 {
                        v___x_956_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__14_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__14,
                        );
                        v___y_924_ = v___x_956_;
                        state = 7;
                        continue;
                    } else {
                        v___x_957_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprWeekday_repr___closed__15_once
                            ),
                            _init_l_Std_Time_instReprWeekday_repr___closed__15,
                        );
                        v___y_924_ = v___x_957_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v___x_883_ = l_Std_Time_instReprWeekday_repr___closed__1;
                lean_inc(v___y_882_);
                v___x_884_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_884_, 0, v___y_882_);
                lean_ctor_set(v___x_884_, 1, v___x_883_);
                v___x_885_ = 0;
                v___x_886_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_886_, 0, v___x_884_);
                lean_ctor_set_uint8(
                    v___x_886_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_885_,
                );
                v___x_887_ = l_Repr_addAppParen(v___x_886_, v_prec_880_);
                return v___x_887_;
            }
            2 => {
                v___x_890_ = l_Std_Time_instReprWeekday_repr___closed__3;
                lean_inc(v___y_889_);
                v___x_891_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_891_, 0, v___y_889_);
                lean_ctor_set(v___x_891_, 1, v___x_890_);
                v___x_892_ = 0;
                v___x_893_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_893_, 0, v___x_891_);
                lean_ctor_set_uint8(
                    v___x_893_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_892_,
                );
                v___x_894_ = l_Repr_addAppParen(v___x_893_, v_prec_880_);
                return v___x_894_;
            }
            3 => {
                v___x_897_ = l_Std_Time_instReprWeekday_repr___closed__5;
                lean_inc(v___y_896_);
                v___x_898_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_898_, 0, v___y_896_);
                lean_ctor_set(v___x_898_, 1, v___x_897_);
                v___x_899_ = 0;
                v___x_900_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_900_, 0, v___x_898_);
                lean_ctor_set_uint8(
                    v___x_900_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_899_,
                );
                v___x_901_ = l_Repr_addAppParen(v___x_900_, v_prec_880_);
                return v___x_901_;
            }
            4 => {
                v___x_904_ = l_Std_Time_instReprWeekday_repr___closed__7;
                lean_inc(v___y_903_);
                v___x_905_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_905_, 0, v___y_903_);
                lean_ctor_set(v___x_905_, 1, v___x_904_);
                v___x_906_ = 0;
                v___x_907_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_907_, 0, v___x_905_);
                lean_ctor_set_uint8(
                    v___x_907_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_906_,
                );
                v___x_908_ = l_Repr_addAppParen(v___x_907_, v_prec_880_);
                return v___x_908_;
            }
            5 => {
                v___x_911_ = l_Std_Time_instReprWeekday_repr___closed__9;
                lean_inc(v___y_910_);
                v___x_912_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_912_, 0, v___y_910_);
                lean_ctor_set(v___x_912_, 1, v___x_911_);
                v___x_913_ = 0;
                v___x_914_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_914_, 0, v___x_912_);
                lean_ctor_set_uint8(
                    v___x_914_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_913_,
                );
                v___x_915_ = l_Repr_addAppParen(v___x_914_, v_prec_880_);
                return v___x_915_;
            }
            6 => {
                v___x_918_ = l_Std_Time_instReprWeekday_repr___closed__11;
                lean_inc(v___y_917_);
                v___x_919_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_919_, 0, v___y_917_);
                lean_ctor_set(v___x_919_, 1, v___x_918_);
                v___x_920_ = 0;
                v___x_921_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_921_, 0, v___x_919_);
                lean_ctor_set_uint8(
                    v___x_921_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_920_,
                );
                v___x_922_ = l_Repr_addAppParen(v___x_921_, v_prec_880_);
                return v___x_922_;
            }
            7 => {
                v___x_925_ = l_Std_Time_instReprWeekday_repr___closed__13;
                lean_inc(v___y_924_);
                v___x_926_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_926_, 0, v___y_924_);
                lean_ctor_set(v___x_926_, 1, v___x_925_);
                v___x_927_ = 0;
                v___x_928_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_928_, 0, v___x_926_);
                lean_ctor_set_uint8(
                    v___x_928_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_927_,
                );
                v___x_929_ = l_Repr_addAppParen(v___x_928_, v_prec_880_);
                return v___x_929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprWeekday_repr___boxed(
    mut v_x_958_: *mut LeanObject,
    mut v_prec_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_401__boxed_960_: u8 = 0;
    let mut v_res_961_: *mut LeanObject = core::ptr::null_mut();
    v_x_401__boxed_960_ = (lean_unbox(v_x_958_) as u8);
    v_res_961_ = l_Std_Time_instReprWeekday_repr(v_x_401__boxed_960_, v_prec_959_);
    lean_dec(v_prec_959_);
    return v_res_961_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWeekday_default() -> u8 {
    let mut v___x_964_: u8 = 0;
    v___x_964_ = 0;
    return v___x_964_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWeekday() -> u8 {
    let mut v___x_965_: u8 = 0;
    v___x_965_ = 0;
    return v___x_965_;
}
pub unsafe fn l_Std_Time_Weekday_ofNat(mut v_n_966_: *mut LeanObject) -> u8 {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    v___x_967_ = lean_unsigned_to_nat(2);
    v___x_968_ = lean_nat_dec_le(v_n_966_, v___x_967_);
    if v___x_968_ == 0 {
        let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_970_: u8 = 0;
        v___x_969_ = lean_unsigned_to_nat(4);
        v___x_970_ = lean_nat_dec_le(v_n_966_, v___x_969_);
        if v___x_970_ == 0 {
            let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_972_: u8 = 0;
            v___x_971_ = lean_unsigned_to_nat(5);
            v___x_972_ = lean_nat_dec_le(v_n_966_, v___x_971_);
            if v___x_972_ == 0 {
                let mut v___x_973_: u8 = 0;
                v___x_973_ = 6;
                return v___x_973_;
            } else {
                let mut v___x_974_: u8 = 0;
                v___x_974_ = 5;
                return v___x_974_;
            }
        } else {
            let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_976_: u8 = 0;
            v___x_975_ = lean_unsigned_to_nat(3);
            v___x_976_ = lean_nat_dec_le(v_n_966_, v___x_975_);
            if v___x_976_ == 0 {
                let mut v___x_977_: u8 = 0;
                v___x_977_ = 4;
                return v___x_977_;
            } else {
                let mut v___x_978_: u8 = 0;
                v___x_978_ = 3;
                return v___x_978_;
            }
        }
    } else {
        let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: u8 = 0;
        v___x_979_ = lean_unsigned_to_nat(0);
        v___x_980_ = lean_nat_dec_le(v_n_966_, v___x_979_);
        if v___x_980_ == 0 {
            let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_982_: u8 = 0;
            v___x_981_ = lean_unsigned_to_nat(1);
            v___x_982_ = lean_nat_dec_le(v_n_966_, v___x_981_);
            if v___x_982_ == 0 {
                let mut v___x_983_: u8 = 0;
                v___x_983_ = 2;
                return v___x_983_;
            } else {
                let mut v___x_984_: u8 = 0;
                v___x_984_ = 1;
                return v___x_984_;
            }
        } else {
            let mut v___x_985_: u8 = 0;
            v___x_985_ = 0;
            return v___x_985_;
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_ofNat___boxed(mut v_n_986_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_987_: u8 = 0;
    let mut v_r_988_: *mut LeanObject = core::ptr::null_mut();
    v_res_987_ = l_Std_Time_Weekday_ofNat(v_n_986_);
    lean_dec(v_n_986_);
    v_r_988_ = lean_box((v_res_987_) as usize);
    return v_r_988_;
}
pub unsafe fn l_Std_Time_instDecidableEqWeekday(mut v_x_989_: u8, mut v_y_990_: u8) -> u8 {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: u8 = 0;
    v___x_991_ = l_Std_Time_Weekday_ctorIdx(v_x_989_);
    v___x_992_ = l_Std_Time_Weekday_ctorIdx(v_y_990_);
    v___x_993_ = lean_nat_dec_eq(v___x_991_, v___x_992_);
    lean_dec(v___x_992_);
    lean_dec(v___x_991_);
    return v___x_993_;
}
pub unsafe fn l_Std_Time_instDecidableEqWeekday___boxed(
    mut v_x_994_: *mut LeanObject,
    mut v_y_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_996_: u8 = 0;
    let mut v_y_14__boxed_997_: u8 = 0;
    let mut v_res_998_: u8 = 0;
    let mut v_r_999_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_996_ = (lean_unbox(v_x_994_) as u8);
    v_y_14__boxed_997_ = (lean_unbox(v_y_995_) as u8);
    v_res_998_ = l_Std_Time_instDecidableEqWeekday(v_x_13__boxed_996_, v_y_14__boxed_997_);
    v_r_999_ = lean_box((v_res_998_) as usize);
    return v_r_999_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = lean_unsigned_to_nat(0);
    v___x_1001_ = lean_nat_to_int(v___x_1000_);
    return v___x_1001_;
}
pub unsafe fn l_Std_Time_Weekday_instReprOrdinal___aux__1(
    mut v_n_1002_: *mut LeanObject,
    mut v_a_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: u8 = 0;
    v___x_1004_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1005_ = lean_int_dec_lt(v_n_1002_, v___x_1004_);
    if v___x_1005_ == 0 {
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        v___x_1006_ = l_Int_repr(v_n_1002_);
        v___x_1007_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1007_, 0, v___x_1006_);
        return v___x_1007_;
    } else {
        let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
        v___x_1008_ = l_Int_repr(v_n_1002_);
        v___x_1009_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1009_, 0, v___x_1008_);
        v___x_1010_ = l_Repr_addAppParen(v___x_1009_, v_a_1003_);
        return v___x_1010_;
    }
}
pub unsafe fn l_Std_Time_Weekday_instReprOrdinal___aux__1___boxed(
    mut v_n_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Std_Time_Weekday_instReprOrdinal___aux__1(v_n_1011_, v_a_1012_);
    lean_dec(v_a_1012_);
    lean_dec(v_n_1011_);
    return v_res_1013_;
}
pub unsafe fn l_Std_Time_Weekday_instReprOrdinal___lam__0(
    mut v___y_1014_: *mut LeanObject,
    mut v___y_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: u8 = 0;
    v___x_1016_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1017_ = lean_int_dec_lt(v___y_1014_, v___x_1016_);
    if v___x_1017_ == 0 {
        let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
        v___x_1018_ = l_Int_repr(v___y_1014_);
        v___x_1019_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1019_, 0, v___x_1018_);
        return v___x_1019_;
    } else {
        let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
        v___x_1020_ = l_Int_repr(v___y_1014_);
        v___x_1021_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_1021_, 0, v___x_1020_);
        v___x_1022_ = l_Repr_addAppParen(v___x_1021_, v___y_1015_);
        return v___x_1022_;
    }
}
pub unsafe fn l_Std_Time_Weekday_instReprOrdinal___lam__0___boxed(
    mut v___y_1023_: *mut LeanObject,
    mut v___y_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Std_Time_Weekday_instReprOrdinal___lam__0(v___y_1023_, v___y_1024_);
    lean_dec(v___y_1024_);
    lean_dec(v___y_1023_);
    return v_res_1025_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableEqOrdinal___aux__1(
    mut v_a_1028_: *mut LeanObject,
    mut v_b_1029_: *mut LeanObject,
) -> u8 {
    let mut v___x_1030_: u8 = 0;
    v___x_1030_ = lean_int_dec_eq(v_a_1028_, v_b_1029_);
    return v___x_1030_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_1031_: *mut LeanObject,
    mut v_b_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1033_: u8 = 0;
    let mut v_r_1034_: *mut LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Std_Time_Weekday_instDecidableEqOrdinal___aux__1(v_a_1031_, v_b_1032_);
    lean_dec(v_b_1032_);
    lean_dec(v_a_1031_);
    v_r_1034_ = lean_box((v_res_1033_) as usize);
    return v_r_1034_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableEqOrdinal(
    mut v_a_1035_: *mut LeanObject,
    mut v_b_1036_: *mut LeanObject,
) -> u8 {
    let mut v___x_1037_: u8 = 0;
    v___x_1037_ = lean_int_dec_eq(v_a_1035_, v_b_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableEqOrdinal___boxed(
    mut v_a_1038_: *mut LeanObject,
    mut v_b_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1040_: u8 = 0;
    let mut v_r_1041_: *mut LeanObject = core::ptr::null_mut();
    v_res_1040_ = l_Std_Time_Weekday_instDecidableEqOrdinal(v_a_1038_, v_b_1039_);
    lean_dec(v_b_1039_);
    lean_dec(v_a_1038_);
    v_r_1041_ = lean_box((v_res_1040_) as usize);
    return v_r_1041_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instLTOrdinal() -> *mut LeanObject {
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    v___x_1042_ = lean_box(0);
    return v___x_1042_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instLEOrdinal() -> *mut LeanObject {
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = lean_box(0);
    return v___x_1043_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLeOrdinal___aux__1(
    mut v_x_1044_: *mut LeanObject,
    mut v_y_1045_: *mut LeanObject,
) -> u8 {
    let mut v___x_1046_: u8 = 0;
    v___x_1046_ = lean_int_dec_le(v_x_1044_, v_y_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_1047_: *mut LeanObject,
    mut v_y_1048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1049_: u8 = 0;
    let mut v_r_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Std_Time_Weekday_instDecidableLeOrdinal___aux__1(v_x_1047_, v_y_1048_);
    lean_dec(v_y_1048_);
    lean_dec(v_x_1047_);
    v_r_1050_ = lean_box((v_res_1049_) as usize);
    return v_r_1050_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLeOrdinal(
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
) -> u8 {
    let mut v___x_1053_: u8 = 0;
    v___x_1053_ = lean_int_dec_le(v___y_1051_, v___y_1052_);
    return v___x_1053_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLeOrdinal___boxed(
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: u8 = 0;
    let mut v_r_1057_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l_Std_Time_Weekday_instDecidableLeOrdinal(v___y_1054_, v___y_1055_);
    lean_dec(v___y_1055_);
    lean_dec(v___y_1054_);
    v_r_1057_ = lean_box((v_res_1056_) as usize);
    return v_r_1057_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLtOrdinal___aux__1(
    mut v_x_1058_: *mut LeanObject,
    mut v_y_1059_: *mut LeanObject,
) -> u8 {
    let mut v___x_1060_: u8 = 0;
    v___x_1060_ = lean_int_dec_lt(v_x_1058_, v_y_1059_);
    return v___x_1060_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_1061_: *mut LeanObject,
    mut v_y_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1063_: u8 = 0;
    let mut v_r_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Std_Time_Weekday_instDecidableLtOrdinal___aux__1(v_x_1061_, v_y_1062_);
    lean_dec(v_y_1062_);
    lean_dec(v_x_1061_);
    v_r_1064_ = lean_box((v_res_1063_) as usize);
    return v_r_1064_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLtOrdinal(
    mut v___y_1065_: *mut LeanObject,
    mut v___y_1066_: *mut LeanObject,
) -> u8 {
    let mut v___x_1067_: u8 = 0;
    v___x_1067_ = lean_int_dec_lt(v___y_1065_, v___y_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Std_Time_Weekday_instDecidableLtOrdinal___boxed(
    mut v___y_1068_: *mut LeanObject,
    mut v___y_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1070_: u8 = 0;
    let mut v_r_1071_: *mut LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_Std_Time_Weekday_instDecidableLtOrdinal(v___y_1068_, v___y_1069_);
    lean_dec(v___y_1069_);
    lean_dec(v___y_1068_);
    v_r_1071_ = lean_box((v_res_1070_) as usize);
    return v_r_1071_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_unsigned_to_nat(6);
    v___x_1073_ = lean_nat_to_int(v___x_1072_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__1() -> *mut LeanObject {
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    v___x_1074_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1075_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1076_ = lean_int_add(v___x_1075_, v___x_1074_);
    return v___x_1076_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__2() -> *mut LeanObject {
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    v___x_1077_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1078_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_1079_ = lean_int_sub(v___x_1078_, v___x_1077_);
    return v___x_1079_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3() -> *mut LeanObject {
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1082_: *mut LeanObject = core::ptr::null_mut();
    v___x_1080_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1081_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__2,
    );
    v_range_1082_ = lean_int_add(v___x_1081_, v___x_1080_);
    return v_range_1082_;
}
pub unsafe fn l_Std_Time_Weekday_instOfNatOrdinal___aux__1(
    mut v_n_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    v___x_1084_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1085_ = lean_nat_to_int(v_n_1083_);
    v_range_1086_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_1087_ = lean_int_sub(v___x_1085_, v___x_1084_);
    lean_dec(v___x_1085_);
    v___x_1088_ = lean_int_emod(v___x_1087_, v_range_1086_);
    lean_dec(v___x_1087_);
    v___x_1089_ = lean_int_add(v___x_1088_, v_range_1086_);
    lean_dec(v___x_1088_);
    v___x_1090_ = lean_int_emod(v___x_1089_, v_range_1086_);
    lean_dec(v___x_1089_);
    v___x_1091_ = lean_int_add(v___x_1090_, v___x_1084_);
    lean_dec(v___x_1090_);
    return v___x_1091_;
}
pub unsafe fn l_Std_Time_Weekday_instOfNatOrdinal(
    mut v_n_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    v___x_1093_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1094_ = lean_nat_to_int(v_n_1092_);
    v_range_1095_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_1096_ = lean_int_sub(v___x_1094_, v___x_1093_);
    lean_dec(v___x_1094_);
    v___x_1097_ = lean_int_emod(v___x_1096_, v_range_1095_);
    lean_dec(v___x_1096_);
    v___x_1098_ = lean_int_add(v___x_1097_, v_range_1095_);
    lean_dec(v___x_1097_);
    v___x_1099_ = lean_int_emod(v___x_1098_, v_range_1095_);
    lean_dec(v___x_1098_);
    v___x_1100_ = lean_int_add(v___x_1099_, v___x_1093_);
    lean_dec(v___x_1099_);
    return v___x_1100_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__0() -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1102_ = lean_int_sub(v___x_1101_, v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__1() -> *mut LeanObject {
    let mut v_range_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    v_range_1103_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_1104_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__0,
    );
    v___x_1105_ = lean_int_emod(v___x_1104_, v_range_1103_);
    return v___x_1105_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__2() -> *mut LeanObject {
    let mut v_range_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v_range_1106_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_1107_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__1,
    );
    v___x_1108_ = lean_int_add(v___x_1107_, v_range_1106_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__3() -> *mut LeanObject {
    let mut v_range_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v_range_1109_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Weekday_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_1110_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__2,
    );
    v___x_1111_ = lean_int_emod(v___x_1110_, v_range_1109_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__4() -> *mut LeanObject {
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    v___x_1112_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1113_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__3,
    );
    v___x_1114_ = lean_int_add(v___x_1113_, v___x_1112_);
    return v___x_1114_;
}
pub unsafe fn _init_l_Std_Time_Weekday_instInhabitedOrdinal() -> *mut LeanObject {
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1115_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__4,
    );
    return v___x_1115_;
}
pub unsafe fn l_Std_Time_Weekday_instOrdOrdinal___aux__1(
    mut v_x_1116_: *mut LeanObject,
    mut v_y_1117_: *mut LeanObject,
) -> u8 {
    let mut v___x_1118_: u8 = 0;
    v___x_1118_ = lean_int_dec_lt(v_x_1116_, v_y_1117_);
    if v___x_1118_ == 0 {
        let mut v___x_1119_: u8 = 0;
        v___x_1119_ = lean_int_dec_eq(v_x_1116_, v_y_1117_);
        if v___x_1119_ == 0 {
            let mut v___x_1120_: u8 = 0;
            v___x_1120_ = 2;
            return v___x_1120_;
        } else {
            let mut v___x_1121_: u8 = 0;
            v___x_1121_ = 1;
            return v___x_1121_;
        }
    } else {
        let mut v___x_1122_: u8 = 0;
        v___x_1122_ = 0;
        return v___x_1122_;
    }
}
pub unsafe fn l_Std_Time_Weekday_instOrdOrdinal___aux__1___boxed(
    mut v_x_1123_: *mut LeanObject,
    mut v_y_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1125_: u8 = 0;
    let mut v_r_1126_: *mut LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Std_Time_Weekday_instOrdOrdinal___aux__1(v_x_1123_, v_y_1124_);
    lean_dec(v_y_1124_);
    lean_dec(v_x_1123_);
    v_r_1126_ = lean_box((v_res_1125_) as usize);
    return v_r_1126_;
}
pub unsafe fn l_Std_Time_Weekday_ofOrdinal(mut v_x_1129_: *mut LeanObject) -> u8 {
    let mut v_natZero_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1132_: u8 = 0;
    let mut v_a_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1134_: u8 = 0;
    let mut v_one_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1137_: u8 = 0;
    v_natZero_1130_ = lean_unsigned_to_nat(0);
    v_intZero_1131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Weekday_instReprOrdinal___aux__1___closed__0,
    );
    v_isNeg_1132_ = lean_int_dec_lt(v_x_1129_, v_intZero_1131_);
    v_a_1133_ = lean_nat_abs(v_x_1129_);
    v_isZero_1134_ = lean_nat_dec_eq(v_a_1133_, v_natZero_1130_);
    v_one_1135_ = lean_unsigned_to_nat(1);
    v_n_1136_ = lean_nat_sub(v_a_1133_, v_one_1135_);
    lean_dec(v_a_1133_);
    v_isZero_1137_ = lean_nat_dec_eq(v_n_1136_, v_natZero_1130_);
    if v_isZero_1137_ == 1 {
        let mut v___x_1138_: u8 = 0;
        lean_dec(v_n_1136_);
        v___x_1138_ = 0;
        return v___x_1138_;
    } else {
        let mut v_n_1139_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1140_: u8 = 0;
        v_n_1139_ = lean_nat_sub(v_n_1136_, v_one_1135_);
        lean_dec(v_n_1136_);
        v_isZero_1140_ = lean_nat_dec_eq(v_n_1139_, v_natZero_1130_);
        if v_isZero_1140_ == 1 {
            let mut v___x_1141_: u8 = 0;
            lean_dec(v_n_1139_);
            v___x_1141_ = 1;
            return v___x_1141_;
        } else {
            let mut v_n_1142_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isZero_1143_: u8 = 0;
            v_n_1142_ = lean_nat_sub(v_n_1139_, v_one_1135_);
            lean_dec(v_n_1139_);
            v_isZero_1143_ = lean_nat_dec_eq(v_n_1142_, v_natZero_1130_);
            if v_isZero_1143_ == 1 {
                let mut v___x_1144_: u8 = 0;
                lean_dec(v_n_1142_);
                v___x_1144_ = 2;
                return v___x_1144_;
            } else {
                let mut v_n_1145_: *mut LeanObject = core::ptr::null_mut();
                let mut v_isZero_1146_: u8 = 0;
                v_n_1145_ = lean_nat_sub(v_n_1142_, v_one_1135_);
                lean_dec(v_n_1142_);
                v_isZero_1146_ = lean_nat_dec_eq(v_n_1145_, v_natZero_1130_);
                if v_isZero_1146_ == 1 {
                    let mut v___x_1147_: u8 = 0;
                    lean_dec(v_n_1145_);
                    v___x_1147_ = 3;
                    return v___x_1147_;
                } else {
                    let mut v_n_1148_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_isZero_1149_: u8 = 0;
                    v_n_1148_ = lean_nat_sub(v_n_1145_, v_one_1135_);
                    lean_dec(v_n_1145_);
                    v_isZero_1149_ = lean_nat_dec_eq(v_n_1148_, v_natZero_1130_);
                    if v_isZero_1149_ == 1 {
                        let mut v___x_1150_: u8 = 0;
                        lean_dec(v_n_1148_);
                        v___x_1150_ = 4;
                        return v___x_1150_;
                    } else {
                        let mut v_n_1151_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_isZero_1152_: u8 = 0;
                        v_n_1151_ = lean_nat_sub(v_n_1148_, v_one_1135_);
                        lean_dec(v_n_1148_);
                        v_isZero_1152_ = lean_nat_dec_eq(v_n_1151_, v_natZero_1130_);
                        if v_isZero_1152_ == 1 {
                            let mut v___x_1153_: u8 = 0;
                            lean_dec(v_n_1151_);
                            v___x_1153_ = 5;
                            return v___x_1153_;
                        } else {
                            let mut v_n_1154_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_isZero_1155_: u8 = 0;
                            let mut v___x_1156_: u8 = 0;
                            v_n_1154_ = lean_nat_sub(v_n_1151_, v_one_1135_);
                            lean_dec(v_n_1151_);
                            v_isZero_1155_ = lean_nat_dec_eq(v_n_1154_, v_natZero_1130_);
                            lean_dec(v_n_1154_);
                            v___x_1156_ = 6;
                            return v___x_1156_;
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_ofOrdinal___boxed(
    mut v_x_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1158_: u8 = 0;
    let mut v_r_1159_: *mut LeanObject = core::ptr::null_mut();
    v_res_1158_ = l_Std_Time_Weekday_ofOrdinal(v_x_1157_);
    lean_dec(v_x_1157_);
    v_r_1159_ = lean_box((v_res_1158_) as usize);
    return v_r_1159_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Weekday_toOrdinal_spec__0(
    mut v_a_1160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ = lean_nat_to_int(v_a_1160_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__0() -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = lean_unsigned_to_nat(6);
    v___x_1163_ = lean_nat_to_int(v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__1() -> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1164_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__0_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__0,
    );
    v___x_1165_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1166_ = lean_int_add(v___x_1165_, v___x_1164_);
    return v___x_1166_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__2() -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    v___x_1167_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1168_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__1_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__1,
    );
    v___x_1169_ = lean_int_sub(v___x_1168_, v___x_1167_);
    return v___x_1169_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__3() -> *mut LeanObject {
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1170_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1171_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__2_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__2,
    );
    v_range_1172_ = lean_int_add(v___x_1171_, v___x_1170_);
    return v_range_1172_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__4() -> *mut LeanObject {
    let mut v_range_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v_range_1173_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1174_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__0,
    );
    v___x_1175_ = lean_int_emod(v___x_1174_, v_range_1173_);
    return v___x_1175_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__5() -> *mut LeanObject {
    let mut v_range_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    v_range_1176_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1177_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__4_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__4,
    );
    v___x_1178_ = lean_int_add(v___x_1177_, v_range_1176_);
    return v___x_1178_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__6() -> *mut LeanObject {
    let mut v_range_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    v_range_1179_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1180_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__5_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__5,
    );
    v___x_1181_ = lean_int_emod(v___x_1180_, v_range_1179_);
    return v___x_1181_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__7() -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__6_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__6,
    );
    v___x_1184_ = lean_int_add(v___x_1183_, v___x_1182_);
    return v___x_1184_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__8() -> *mut LeanObject {
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v___x_1185_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1186_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__14_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__14,
    );
    v___x_1187_ = lean_int_sub(v___x_1186_, v___x_1185_);
    return v___x_1187_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__9() -> *mut LeanObject {
    let mut v_range_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    v_range_1188_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1189_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__8_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__8,
    );
    v___x_1190_ = lean_int_emod(v___x_1189_, v_range_1188_);
    return v___x_1190_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__10() -> *mut LeanObject {
    let mut v_range_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v_range_1191_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1192_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__9_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__9,
    );
    v___x_1193_ = lean_int_add(v___x_1192_, v_range_1191_);
    return v___x_1193_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__11() -> *mut LeanObject {
    let mut v_range_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    v_range_1194_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1195_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__10_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__10,
    );
    v___x_1196_ = lean_int_emod(v___x_1195_, v_range_1194_);
    return v___x_1196_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__12() -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1198_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__11_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__11,
    );
    v___x_1199_ = lean_int_add(v___x_1198_, v___x_1197_);
    return v___x_1199_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__13() -> *mut LeanObject {
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1200_ = lean_unsigned_to_nat(3);
    v___x_1201_ = lean_nat_to_int(v___x_1200_);
    return v___x_1201_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__14() -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1203_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__13_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__13,
    );
    v___x_1204_ = lean_int_sub(v___x_1203_, v___x_1202_);
    return v___x_1204_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__15() -> *mut LeanObject {
    let mut v_range_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    v_range_1205_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1206_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__14_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__14,
    );
    v___x_1207_ = lean_int_emod(v___x_1206_, v_range_1205_);
    return v___x_1207_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__16() -> *mut LeanObject {
    let mut v_range_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    v_range_1208_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1209_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__15_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__15,
    );
    v___x_1210_ = lean_int_add(v___x_1209_, v_range_1208_);
    return v___x_1210_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__17() -> *mut LeanObject {
    let mut v_range_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    v_range_1211_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1212_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__16_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__16,
    );
    v___x_1213_ = lean_int_emod(v___x_1212_, v_range_1211_);
    return v___x_1213_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__18() -> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1214_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1215_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__17_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__17,
    );
    v___x_1216_ = lean_int_add(v___x_1215_, v___x_1214_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__19() -> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ = lean_unsigned_to_nat(4);
    v___x_1218_ = lean_nat_to_int(v___x_1217_);
    return v___x_1218_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__20() -> *mut LeanObject {
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    v___x_1219_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1220_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__19_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__19,
    );
    v___x_1221_ = lean_int_sub(v___x_1220_, v___x_1219_);
    return v___x_1221_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__21() -> *mut LeanObject {
    let mut v_range_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v_range_1222_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1223_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__20_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__20,
    );
    v___x_1224_ = lean_int_emod(v___x_1223_, v_range_1222_);
    return v___x_1224_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__22() -> *mut LeanObject {
    let mut v_range_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    v_range_1225_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1226_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__21_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__21,
    );
    v___x_1227_ = lean_int_add(v___x_1226_, v_range_1225_);
    return v___x_1227_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__23() -> *mut LeanObject {
    let mut v_range_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    v_range_1228_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1229_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__22_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__22,
    );
    v___x_1230_ = lean_int_emod(v___x_1229_, v_range_1228_);
    return v___x_1230_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__24() -> *mut LeanObject {
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    v___x_1231_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1232_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__23_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__23,
    );
    v___x_1233_ = lean_int_add(v___x_1232_, v___x_1231_);
    return v___x_1233_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__25() -> *mut LeanObject {
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v___x_1234_ = lean_unsigned_to_nat(5);
    v___x_1235_ = lean_nat_to_int(v___x_1234_);
    return v___x_1235_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__26() -> *mut LeanObject {
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1236_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1237_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__25_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__25,
    );
    v___x_1238_ = lean_int_sub(v___x_1237_, v___x_1236_);
    return v___x_1238_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__27() -> *mut LeanObject {
    let mut v_range_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    v_range_1239_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1240_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__26_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__26,
    );
    v___x_1241_ = lean_int_emod(v___x_1240_, v_range_1239_);
    return v___x_1241_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__28() -> *mut LeanObject {
    let mut v_range_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    v_range_1242_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1243_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__27),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__27_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__27,
    );
    v___x_1244_ = lean_int_add(v___x_1243_, v_range_1242_);
    return v___x_1244_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__29() -> *mut LeanObject {
    let mut v_range_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    v_range_1245_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1246_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__28),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__28_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__28,
    );
    v___x_1247_ = lean_int_emod(v___x_1246_, v_range_1245_);
    return v___x_1247_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__30() -> *mut LeanObject {
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    v___x_1248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1249_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__29),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__29_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__29,
    );
    v___x_1250_ = lean_int_add(v___x_1249_, v___x_1248_);
    return v___x_1250_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__31() -> *mut LeanObject {
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    v___x_1251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1252_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__0_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__0,
    );
    v___x_1253_ = lean_int_sub(v___x_1252_, v___x_1251_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__32() -> *mut LeanObject {
    let mut v_range_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v_range_1254_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__31),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__31_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__31,
    );
    v___x_1256_ = lean_int_emod(v___x_1255_, v_range_1254_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__33() -> *mut LeanObject {
    let mut v_range_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    v_range_1257_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1258_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__32_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__32,
    );
    v___x_1259_ = lean_int_add(v___x_1258_, v_range_1257_);
    return v___x_1259_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__34() -> *mut LeanObject {
    let mut v_range_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    v_range_1260_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1261_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__33),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__33_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__33,
    );
    v___x_1262_ = lean_int_emod(v___x_1261_, v_range_1260_);
    return v___x_1262_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__35() -> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1264_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__34),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__34_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__34,
    );
    v___x_1265_ = lean_int_add(v___x_1264_, v___x_1263_);
    return v___x_1265_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__36() -> *mut LeanObject {
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    v___x_1266_ = lean_unsigned_to_nat(7);
    v___x_1267_ = lean_nat_to_int(v___x_1266_);
    return v___x_1267_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__37() -> *mut LeanObject {
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    v___x_1268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1269_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__36),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__36_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__36,
    );
    v___x_1270_ = lean_int_sub(v___x_1269_, v___x_1268_);
    return v___x_1270_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__38() -> *mut LeanObject {
    let mut v_range_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v_range_1271_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1272_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__37),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__37_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__37,
    );
    v___x_1273_ = lean_int_emod(v___x_1272_, v_range_1271_);
    return v___x_1273_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__39() -> *mut LeanObject {
    let mut v_range_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v_range_1274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1275_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__38),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__38_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__38,
    );
    v___x_1276_ = lean_int_add(v___x_1275_, v_range_1274_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__40() -> *mut LeanObject {
    let mut v_range_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    v_range_1277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__3_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__3,
    );
    v___x_1278_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__39),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__39_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__39,
    );
    v___x_1279_ = lean_int_emod(v___x_1278_, v_range_1277_);
    return v___x_1279_;
}
pub unsafe fn _init_l_Std_Time_Weekday_toOrdinal___closed__41() -> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1280_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWeekday_repr___closed__15_once),
        _init_l_Std_Time_instReprWeekday_repr___closed__15,
    );
    v___x_1281_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__40),
        core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__40_once),
        _init_l_Std_Time_Weekday_toOrdinal___closed__40,
    );
    v___x_1282_ = lean_int_add(v___x_1281_, v___x_1280_);
    return v___x_1282_;
}
pub unsafe fn l_Std_Time_Weekday_toOrdinal(mut v_x_1283_: u8) -> *mut LeanObject {
    match v_x_1283_ {
        0 => {
            let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
            v___x_1284_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__7),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__7_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__7,
            );
            return v___x_1284_;
        }
        1 => {
            let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
            v___x_1285_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__12),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__12_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__12,
            );
            return v___x_1285_;
        }
        2 => {
            let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
            v___x_1286_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__18),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__18_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__18,
            );
            return v___x_1286_;
        }
        3 => {
            let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
            v___x_1287_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__24),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__24_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__24,
            );
            return v___x_1287_;
        }
        4 => {
            let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
            v___x_1288_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__30),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__30_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__30,
            );
            return v___x_1288_;
        }
        5 => {
            let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
            v___x_1289_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__35),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__35_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__35,
            );
            return v___x_1289_;
        }
        _ => {
            let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
            v___x_1290_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__41),
                core::ptr::addr_of_mut!(l_Std_Time_Weekday_toOrdinal___closed__41_once),
                _init_l_Std_Time_Weekday_toOrdinal___closed__41,
            );
            return v___x_1290_;
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_toOrdinal___boxed(
    mut v_x_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_576__boxed_1292_: u8 = 0;
    let mut v_res_1293_: *mut LeanObject = core::ptr::null_mut();
    v_x_576__boxed_1292_ = (lean_unbox(v_x_1291_) as u8);
    v_res_1293_ = l_Std_Time_Weekday_toOrdinal(v_x_576__boxed_1292_);
    return v_res_1293_;
}
pub unsafe fn l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg(
    mut v_x_1299_: u8,
    mut v_h__1_1300_: *mut LeanObject,
    mut v_h__2_1301_: *mut LeanObject,
    mut v_h__3_1302_: *mut LeanObject,
    mut v_h__4_1303_: *mut LeanObject,
    mut v_h__5_1304_: *mut LeanObject,
    mut v_h__6_1305_: *mut LeanObject,
    mut v_h__7_1306_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1299_ {
        0 => {
            let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1306_);
            lean_dec(v_h__6_1305_);
            lean_dec(v_h__5_1304_);
            lean_dec(v_h__4_1303_);
            lean_dec(v_h__3_1302_);
            lean_dec(v_h__2_1301_);
            v___x_1307_ = lean_box(0);
            v___x_1308_ = lean_apply_1(v_h__1_1300_, v___x_1307_);
            return v___x_1308_;
        }
        1 => {
            let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1306_);
            lean_dec(v_h__6_1305_);
            lean_dec(v_h__5_1304_);
            lean_dec(v_h__4_1303_);
            lean_dec(v_h__3_1302_);
            lean_dec(v_h__1_1300_);
            v___x_1309_ = lean_box(0);
            v___x_1310_ = lean_apply_1(v_h__2_1301_, v___x_1309_);
            return v___x_1310_;
        }
        2 => {
            let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1306_);
            lean_dec(v_h__6_1305_);
            lean_dec(v_h__5_1304_);
            lean_dec(v_h__4_1303_);
            lean_dec(v_h__2_1301_);
            lean_dec(v_h__1_1300_);
            v___x_1311_ = lean_box(0);
            v___x_1312_ = lean_apply_1(v_h__3_1302_, v___x_1311_);
            return v___x_1312_;
        }
        3 => {
            let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1306_);
            lean_dec(v_h__6_1305_);
            lean_dec(v_h__5_1304_);
            lean_dec(v_h__3_1302_);
            lean_dec(v_h__2_1301_);
            lean_dec(v_h__1_1300_);
            v___x_1313_ = lean_box(0);
            v___x_1314_ = lean_apply_1(v_h__4_1303_, v___x_1313_);
            return v___x_1314_;
        }
        4 => {
            let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1306_);
            lean_dec(v_h__6_1305_);
            lean_dec(v_h__4_1303_);
            lean_dec(v_h__3_1302_);
            lean_dec(v_h__2_1301_);
            lean_dec(v_h__1_1300_);
            v___x_1315_ = lean_box(0);
            v___x_1316_ = lean_apply_1(v_h__5_1304_, v___x_1315_);
            return v___x_1316_;
        }
        5 => {
            let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1306_);
            lean_dec(v_h__5_1304_);
            lean_dec(v_h__4_1303_);
            lean_dec(v_h__3_1302_);
            lean_dec(v_h__2_1301_);
            lean_dec(v_h__1_1300_);
            v___x_1317_ = lean_box(0);
            v___x_1318_ = lean_apply_1(v_h__6_1305_, v___x_1317_);
            return v___x_1318_;
        }
        _ => {
            let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_1305_);
            lean_dec(v_h__5_1304_);
            lean_dec(v_h__4_1303_);
            lean_dec(v_h__3_1302_);
            lean_dec(v_h__2_1301_);
            lean_dec(v_h__1_1300_);
            v___x_1319_ = lean_box(0);
            v___x_1320_ = lean_apply_1(v_h__7_1306_, v___x_1319_);
            return v___x_1320_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg___boxed(
    mut v_x_1321_: *mut LeanObject,
    mut v_h__1_1322_: *mut LeanObject,
    mut v_h__2_1323_: *mut LeanObject,
    mut v_h__3_1324_: *mut LeanObject,
    mut v_h__4_1325_: *mut LeanObject,
    mut v_h__5_1326_: *mut LeanObject,
    mut v_h__6_1327_: *mut LeanObject,
    mut v_h__7_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_76__boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_x_76__boxed_1329_ = (lean_unbox(v_x_1321_) as u8);
    v_res_1330_ = l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg(v_x_76__boxed_1329_, v_h__1_1322_, v_h__2_1323_, v_h__3_1324_, v_h__4_1325_, v_h__5_1326_, v_h__6_1327_, v_h__7_1328_);
    return v_res_1330_;
}
pub unsafe fn l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter(
    mut v_motive_1331_: *mut LeanObject,
    mut v_x_1332_: u8,
    mut v_h__1_1333_: *mut LeanObject,
    mut v_h__2_1334_: *mut LeanObject,
    mut v_h__3_1335_: *mut LeanObject,
    mut v_h__4_1336_: *mut LeanObject,
    mut v_h__5_1337_: *mut LeanObject,
    mut v_h__6_1338_: *mut LeanObject,
    mut v_h__7_1339_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_1332_ {
        0 => {
            let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1339_);
            lean_dec(v_h__6_1338_);
            lean_dec(v_h__5_1337_);
            lean_dec(v_h__4_1336_);
            lean_dec(v_h__3_1335_);
            lean_dec(v_h__2_1334_);
            v___x_1340_ = lean_box(0);
            v___x_1341_ = lean_apply_1(v_h__1_1333_, v___x_1340_);
            return v___x_1341_;
        }
        1 => {
            let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1339_);
            lean_dec(v_h__6_1338_);
            lean_dec(v_h__5_1337_);
            lean_dec(v_h__4_1336_);
            lean_dec(v_h__3_1335_);
            lean_dec(v_h__1_1333_);
            v___x_1342_ = lean_box(0);
            v___x_1343_ = lean_apply_1(v_h__2_1334_, v___x_1342_);
            return v___x_1343_;
        }
        2 => {
            let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1339_);
            lean_dec(v_h__6_1338_);
            lean_dec(v_h__5_1337_);
            lean_dec(v_h__4_1336_);
            lean_dec(v_h__2_1334_);
            lean_dec(v_h__1_1333_);
            v___x_1344_ = lean_box(0);
            v___x_1345_ = lean_apply_1(v_h__3_1335_, v___x_1344_);
            return v___x_1345_;
        }
        3 => {
            let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1339_);
            lean_dec(v_h__6_1338_);
            lean_dec(v_h__5_1337_);
            lean_dec(v_h__3_1335_);
            lean_dec(v_h__2_1334_);
            lean_dec(v_h__1_1333_);
            v___x_1346_ = lean_box(0);
            v___x_1347_ = lean_apply_1(v_h__4_1336_, v___x_1346_);
            return v___x_1347_;
        }
        4 => {
            let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1339_);
            lean_dec(v_h__6_1338_);
            lean_dec(v_h__4_1336_);
            lean_dec(v_h__3_1335_);
            lean_dec(v_h__2_1334_);
            lean_dec(v_h__1_1333_);
            v___x_1348_ = lean_box(0);
            v___x_1349_ = lean_apply_1(v_h__5_1337_, v___x_1348_);
            return v___x_1349_;
        }
        5 => {
            let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_1339_);
            lean_dec(v_h__5_1337_);
            lean_dec(v_h__4_1336_);
            lean_dec(v_h__3_1335_);
            lean_dec(v_h__2_1334_);
            lean_dec(v_h__1_1333_);
            v___x_1350_ = lean_box(0);
            v___x_1351_ = lean_apply_1(v_h__6_1338_, v___x_1350_);
            return v___x_1351_;
        }
        _ => {
            let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_1338_);
            lean_dec(v_h__5_1337_);
            lean_dec(v_h__4_1336_);
            lean_dec(v_h__3_1335_);
            lean_dec(v_h__2_1334_);
            lean_dec(v_h__1_1333_);
            v___x_1352_ = lean_box(0);
            v___x_1353_ = lean_apply_1(v_h__7_1339_, v___x_1352_);
            return v___x_1353_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___boxed(
    mut v_motive_1354_: *mut LeanObject,
    mut v_x_1355_: *mut LeanObject,
    mut v_h__1_1356_: *mut LeanObject,
    mut v_h__2_1357_: *mut LeanObject,
    mut v_h__3_1358_: *mut LeanObject,
    mut v_h__4_1359_: *mut LeanObject,
    mut v_h__5_1360_: *mut LeanObject,
    mut v_h__6_1361_: *mut LeanObject,
    mut v_h__7_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_107__boxed_1363_: u8 = 0;
    let mut v_res_1364_: *mut LeanObject = core::ptr::null_mut();
    v_x_107__boxed_1363_ = (lean_unbox(v_x_1355_) as u8);
    v_res_1364_ =
        l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter(
            v_motive_1354_,
            v_x_107__boxed_1363_,
            v_h__1_1356_,
            v_h__2_1357_,
            v_h__3_1358_,
            v_h__4_1359_,
            v_h__5_1360_,
            v_h__6_1361_,
            v_h__7_1362_,
        );
    return v_res_1364_;
}
pub unsafe fn l_Std_Time_Weekday_toNat(mut v_x_1365_: u8) -> *mut LeanObject {
    match v_x_1365_ {
        0 => {
            let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
            v___x_1366_ = lean_unsigned_to_nat(1);
            return v___x_1366_;
        }
        1 => {
            let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
            v___x_1367_ = lean_unsigned_to_nat(2);
            return v___x_1367_;
        }
        2 => {
            let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
            v___x_1368_ = lean_unsigned_to_nat(3);
            return v___x_1368_;
        }
        3 => {
            let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
            v___x_1369_ = lean_unsigned_to_nat(4);
            return v___x_1369_;
        }
        4 => {
            let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
            v___x_1370_ = lean_unsigned_to_nat(5);
            return v___x_1370_;
        }
        5 => {
            let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
            v___x_1371_ = lean_unsigned_to_nat(6);
            return v___x_1371_;
        }
        _ => {
            let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
            v___x_1372_ = lean_unsigned_to_nat(7);
            return v___x_1372_;
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_toNat___boxed(mut v_x_1373_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_74__boxed_1374_: u8 = 0;
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_x_74__boxed_1374_ = (lean_unbox(v_x_1373_) as u8);
    v_res_1375_ = l_Std_Time_Weekday_toNat(v_x_74__boxed_1374_);
    return v_res_1375_;
}
pub unsafe fn l_Std_Time_Weekday_ofNat_x3f(mut v_x_1397_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    v___x_1398_ = lean_unsigned_to_nat(1);
    v___x_1399_ = lean_nat_dec_eq(v_x_1397_, v___x_1398_);
    if v___x_1399_ == 0 {
        let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1401_: u8 = 0;
        v___x_1400_ = lean_unsigned_to_nat(2);
        v___x_1401_ = lean_nat_dec_eq(v_x_1397_, v___x_1400_);
        if v___x_1401_ == 0 {
            let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1403_: u8 = 0;
            v___x_1402_ = lean_unsigned_to_nat(3);
            v___x_1403_ = lean_nat_dec_eq(v_x_1397_, v___x_1402_);
            if v___x_1403_ == 0 {
                let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1405_: u8 = 0;
                v___x_1404_ = lean_unsigned_to_nat(4);
                v___x_1405_ = lean_nat_dec_eq(v_x_1397_, v___x_1404_);
                if v___x_1405_ == 0 {
                    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1407_: u8 = 0;
                    v___x_1406_ = lean_unsigned_to_nat(5);
                    v___x_1407_ = lean_nat_dec_eq(v_x_1397_, v___x_1406_);
                    if v___x_1407_ == 0 {
                        let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1409_: u8 = 0;
                        v___x_1408_ = lean_unsigned_to_nat(6);
                        v___x_1409_ = lean_nat_dec_eq(v_x_1397_, v___x_1408_);
                        if v___x_1409_ == 0 {
                            let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_1411_: u8 = 0;
                            v___x_1410_ = lean_unsigned_to_nat(7);
                            v___x_1411_ = lean_nat_dec_eq(v_x_1397_, v___x_1410_);
                            if v___x_1411_ == 0 {
                                let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
                                v___x_1412_ = lean_box(0);
                                return v___x_1412_;
                            } else {
                                let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
                                v___x_1413_ = l_Std_Time_Weekday_ofNat_x3f___closed__0;
                                return v___x_1413_;
                            }
                        } else {
                            let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
                            v___x_1414_ = l_Std_Time_Weekday_ofNat_x3f___closed__1;
                            return v___x_1414_;
                        }
                    } else {
                        let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1415_ = l_Std_Time_Weekday_ofNat_x3f___closed__2;
                        return v___x_1415_;
                    }
                } else {
                    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1416_ = l_Std_Time_Weekday_ofNat_x3f___closed__3;
                    return v___x_1416_;
                }
            } else {
                let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
                v___x_1417_ = l_Std_Time_Weekday_ofNat_x3f___closed__4;
                return v___x_1417_;
            }
        } else {
            let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
            v___x_1418_ = l_Std_Time_Weekday_ofNat_x3f___closed__5;
            return v___x_1418_;
        }
    } else {
        let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
        v___x_1419_ = l_Std_Time_Weekday_ofNat_x3f___closed__6;
        return v___x_1419_;
    }
}
pub unsafe fn l_Std_Time_Weekday_ofNat_x3f___boxed(
    mut v_x_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1421_: *mut LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Std_Time_Weekday_ofNat_x3f(v_x_1420_);
    lean_dec(v_x_1420_);
    return v_res_1421_;
}
pub unsafe fn _init_l_Std_Time_Weekday_ofNat_x21___closed__3() -> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425_ = l_Std_Time_Weekday_ofNat_x21___closed__2;
    v___x_1426_ = lean_unsigned_to_nat(12);
    v___x_1427_ = lean_unsigned_to_nat(139);
    v___x_1428_ = l_Std_Time_Weekday_ofNat_x21___closed__1;
    v___x_1429_ = l_Std_Time_Weekday_ofNat_x21___closed__0;
    v___x_1430_ = l_mkPanicMessageWithDecl(
        v___x_1429_,
        v___x_1428_,
        v___x_1427_,
        v___x_1426_,
        v___x_1425_,
    );
    return v___x_1430_;
}
pub unsafe fn l_Std_Time_Weekday_ofNat_x21(mut v_n_1431_: *mut LeanObject) -> u8 {
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Std_Time_Weekday_ofNat_x3f(v_n_1431_);
    if lean_obj_tag(v___x_1432_) == 0 {
        let mut v___x_1433_: u8 = 0;
        let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: u8 = 0;
        v___x_1433_ = 0;
        v___x_1434_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Weekday_ofNat_x21___closed__3),
            core::ptr::addr_of_mut!(l_Std_Time_Weekday_ofNat_x21___closed__3_once),
            _init_l_Std_Time_Weekday_ofNat_x21___closed__3,
        );
        v___x_1435_ = lean_box((v___x_1433_) as usize);
        v___x_1436_ = l_panic___redArg(v___x_1435_, v___x_1434_);
        lean_dec(v___x_1435_);
        v___x_1437_ = (lean_unbox(v___x_1436_) as u8);
        lean_dec(v___x_1436_);
        return v___x_1437_;
    } else {
        let mut v_val_1438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1439_: u8 = 0;
        v_val_1438_ = lean_ctor_get(v___x_1432_, 0);
        lean_inc(v_val_1438_);
        lean_dec_ref_known(v___x_1432_, 1);
        v___x_1439_ = (lean_unbox(v_val_1438_) as u8);
        lean_dec(v_val_1438_);
        return v___x_1439_;
    }
}
pub unsafe fn l_Std_Time_Weekday_ofNat_x21___boxed(
    mut v_n_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1441_: u8 = 0;
    let mut v_r_1442_: *mut LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Std_Time_Weekday_ofNat_x21(v_n_1440_);
    lean_dec(v_n_1440_);
    v_r_1442_ = lean_box((v_res_1441_) as usize);
    return v_r_1442_;
}
pub unsafe fn l_Std_Time_Weekday_next(mut v_x_1443_: u8) -> u8 {
    match v_x_1443_ {
        0 => {
            let mut v___x_1444_: u8 = 0;
            v___x_1444_ = 1;
            return v___x_1444_;
        }
        1 => {
            let mut v___x_1445_: u8 = 0;
            v___x_1445_ = 2;
            return v___x_1445_;
        }
        2 => {
            let mut v___x_1446_: u8 = 0;
            v___x_1446_ = 3;
            return v___x_1446_;
        }
        3 => {
            let mut v___x_1447_: u8 = 0;
            v___x_1447_ = 4;
            return v___x_1447_;
        }
        4 => {
            let mut v___x_1448_: u8 = 0;
            v___x_1448_ = 5;
            return v___x_1448_;
        }
        5 => {
            let mut v___x_1449_: u8 = 0;
            v___x_1449_ = 6;
            return v___x_1449_;
        }
        _ => {
            let mut v___x_1450_: u8 = 0;
            v___x_1450_ = 0;
            return v___x_1450_;
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_next___boxed(mut v_x_1451_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_53__boxed_1452_: u8 = 0;
    let mut v_res_1453_: u8 = 0;
    let mut v_r_1454_: *mut LeanObject = core::ptr::null_mut();
    v_x_53__boxed_1452_ = (lean_unbox(v_x_1451_) as u8);
    v_res_1453_ = l_Std_Time_Weekday_next(v_x_53__boxed_1452_);
    v_r_1454_ = lean_box((v_res_1453_) as usize);
    return v_r_1454_;
}
pub unsafe fn l_Std_Time_Weekday_isWeekend(mut v_x_1455_: u8) -> u8 {
    match v_x_1455_ {
        5 => {
            let mut v___x_1456_: u8 = 0;
            v___x_1456_ = 1;
            return v___x_1456_;
        }
        6 => {
            let mut v___x_1457_: u8 = 0;
            v___x_1457_ = 1;
            return v___x_1457_;
        }
        _ => {
            let mut v___x_1458_: u8 = 0;
            v___x_1458_ = 0;
            return v___x_1458_;
        }
    }
}
pub unsafe fn l_Std_Time_Weekday_isWeekend___boxed(
    mut v_x_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1460_: u8 = 0;
    let mut v_res_1461_: u8 = 0;
    let mut v_r_1462_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1460_ = (lean_unbox(v_x_1459_) as u8);
    v_res_1461_ = l_Std_Time_Weekday_isWeekend(v_x_26__boxed_1460_);
    v_r_1462_ = lean_box((v_res_1461_) as usize);
    return v_r_1462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Weekday(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_instInhabitedWeekday_default = _init_l_Std_Time_instInhabitedWeekday_default();
    l_Std_Time_instInhabitedWeekday = _init_l_Std_Time_instInhabitedWeekday();
    l_Std_Time_Weekday_instLTOrdinal = _init_l_Std_Time_Weekday_instLTOrdinal();
    lean_mark_persistent(l_Std_Time_Weekday_instLTOrdinal);
    l_Std_Time_Weekday_instLEOrdinal = _init_l_Std_Time_Weekday_instLEOrdinal();
    lean_mark_persistent(l_Std_Time_Weekday_instLEOrdinal);
    l_Std_Time_Weekday_instInhabitedOrdinal = _init_l_Std_Time_Weekday_instInhabitedOrdinal();
    lean_mark_persistent(l_Std_Time_Weekday_instInhabitedOrdinal);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Weekday(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Unit_Weekday(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Day(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Weekday(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Weekday(builtin);
}
