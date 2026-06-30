// Lean compiler output
// Module: Std.Time.Date.Unit.Year
// Imports: Std.Time.Date.Unit.Month
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_ediv, lean_int_emod,
    lean_int_mod, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_dec_le, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Date::Unit::Month::{
    initialize_Std_Time_Date_Unit_Month, runtime_initialize_Std_Time_Date_Unit_Month,
};
pub static l_Std_Time_Year_instReprEra_repr___closed__0_value: leanh::LeanStringObject<22> =
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
            83, 116, 100, 46, 84, 105, 109, 101, 46, 89, 101, 97, 114, 46, 69, 114, 97, 46, 98, 99,
            101, 0,
        ],
    };
static mut l_Std_Time_Year_instReprEra_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprEra_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instReprEra_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Year_instReprEra_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Year_instReprEra_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprEra_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instReprEra_repr___closed__2_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            83, 116, 100, 46, 84, 105, 109, 101, 46, 89, 101, 97, 114, 46, 69, 114, 97, 46, 99,
            101, 0,
        ],
    };
static mut l_Std_Time_Year_instReprEra_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprEra_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instReprEra_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Year_instReprEra_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Year_instReprEra_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprEra_repr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Year_instReprEra_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_instReprEra_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_instReprEra_repr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_instReprEra_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Year_instReprEra___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Year_instReprEra_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instReprEra___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprEra___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instReprEra: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprEra___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instInhabitedEra_default: u8 = 0;
pub static mut l_Std_Time_Year_instInhabitedEra: u8 = 0;
pub static l_Std_Time_Year_instToStringEra___lam__0___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [66, 67, 69, 0],
};
static mut l_Std_Time_Year_instToStringEra___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instToStringEra___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instToStringEra___lam__0___closed__1_value:
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
    m_data: [67, 69, 0],
};
static mut l_Std_Time_Year_instToStringEra___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instToStringEra___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instToStringEra___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Year_instToStringEra___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instToStringEra___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instToStringEra___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instToStringEra: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instToStringEra___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Year_instReprOffset___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_instReprOffset___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Year_instReprOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Year_instReprOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instReprOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instReprOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instReprOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instInhabitedOffset___aux__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Year_instInhabitedOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Year_instAddOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instSubOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instNegOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instNegOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instNegOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instLEOffset: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Year_instLTOffset: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Year_instToStringOffset___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Year_instToStringOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instToStringOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instToStringOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instToStringOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Year_instOrdOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Year_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Year_instOrdOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Year_instOrdOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Year_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Year_Offset_toMonths___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_toMonths___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_isLeap___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_isLeap___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_isLeap___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_isLeap___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_isLeap___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_isLeap___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_days___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_days___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_weeks___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_weeks___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_weeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_weeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Year_Offset_weeks___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Year_Offset_weeks___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Time_Year_Era_ctorIdx(mut v_x_349_: u8) -> *mut leanh::LeanObject {
    if v_x_349_ == 0 {
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_350_ = leanh::lean_unsigned_to_nat(0);
        return v___x_350_;
    } else {
        let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_351_ = leanh::lean_unsigned_to_nat(1);
        return v___x_351_;
    }
}
pub unsafe fn l_Std_Time_Year_Era_ctorIdx___boxed(
    mut v_x_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_353_: u8 = 0;
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_353_ = (leanh::lean_unbox(v_x_352_) as u8);
    v_res_354_ = l_Std_Time_Year_Era_ctorIdx(v_x_boxed_353_);
    return v_res_354_;
}
pub unsafe fn l_Std_Time_Year_Era_toCtorIdx(mut v_x_355_: u8) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Std_Time_Year_Era_ctorIdx(v_x_355_);
    return v___x_356_;
}
pub unsafe fn l_Std_Time_Year_Era_toCtorIdx___boxed(
    mut v_x_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_358_: u8 = 0;
    let mut v_res_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_358_ = (leanh::lean_unbox(v_x_357_) as u8);
    v_res_359_ = l_Std_Time_Year_Era_toCtorIdx(v_x_4__boxed_358_);
    return v_res_359_;
}
pub unsafe fn l_Std_Time_Year_Era_ctorElim___redArg(
    mut v_k_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_360_);
    return v_k_360_;
}
pub unsafe fn l_Std_Time_Year_Era_ctorElim___redArg___boxed(
    mut v_k_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Std_Time_Year_Era_ctorElim___redArg(v_k_361_);
    leanh::lean_dec(v_k_361_);
    return v_res_362_;
}
pub unsafe fn l_Std_Time_Year_Era_ctorElim(
    mut v_motive_363_: *mut leanh::LeanObject,
    mut v_ctorIdx_364_: *mut leanh::LeanObject,
    mut v_t_365_: u8,
    mut v_h_366_: *mut leanh::LeanObject,
    mut v_k_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_367_);
    return v_k_367_;
}
pub unsafe fn l_Std_Time_Year_Era_ctorElim___boxed(
    mut v_motive_368_: *mut leanh::LeanObject,
    mut v_ctorIdx_369_: *mut leanh::LeanObject,
    mut v_t_370_: *mut leanh::LeanObject,
    mut v_h_371_: *mut leanh::LeanObject,
    mut v_k_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_373_: u8 = 0;
    let mut v_res_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_373_ = (leanh::lean_unbox(v_t_370_) as u8);
    v_res_374_ = l_Std_Time_Year_Era_ctorElim(
        v_motive_368_,
        v_ctorIdx_369_,
        v_t_boxed_373_,
        v_h_371_,
        v_k_372_,
    );
    leanh::lean_dec(v_k_372_);
    leanh::lean_dec(v_ctorIdx_369_);
    return v_res_374_;
}
pub unsafe fn l_Std_Time_Year_Era_bce_elim___redArg(
    mut v_bce_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bce_375_);
    return v_bce_375_;
}
pub unsafe fn l_Std_Time_Year_Era_bce_elim___redArg___boxed(
    mut v_bce_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_377_ = l_Std_Time_Year_Era_bce_elim___redArg(v_bce_376_);
    leanh::lean_dec(v_bce_376_);
    return v_res_377_;
}
pub unsafe fn l_Std_Time_Year_Era_bce_elim(
    mut v_motive_378_: *mut leanh::LeanObject,
    mut v_t_379_: u8,
    mut v_h_380_: *mut leanh::LeanObject,
    mut v_bce_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bce_381_);
    return v_bce_381_;
}
pub unsafe fn l_Std_Time_Year_Era_bce_elim___boxed(
    mut v_motive_382_: *mut leanh::LeanObject,
    mut v_t_383_: *mut leanh::LeanObject,
    mut v_h_384_: *mut leanh::LeanObject,
    mut v_bce_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_386_: u8 = 0;
    let mut v_res_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_386_ = (leanh::lean_unbox(v_t_383_) as u8);
    v_res_387_ = l_Std_Time_Year_Era_bce_elim(v_motive_382_, v_t_boxed_386_, v_h_384_, v_bce_385_);
    leanh::lean_dec(v_bce_385_);
    return v_res_387_;
}
pub unsafe fn l_Std_Time_Year_Era_ce_elim___redArg(
    mut v_ce_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ce_388_);
    return v_ce_388_;
}
pub unsafe fn l_Std_Time_Year_Era_ce_elim___redArg___boxed(
    mut v_ce_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Std_Time_Year_Era_ce_elim___redArg(v_ce_389_);
    leanh::lean_dec(v_ce_389_);
    return v_res_390_;
}
pub unsafe fn l_Std_Time_Year_Era_ce_elim(
    mut v_motive_391_: *mut leanh::LeanObject,
    mut v_t_392_: u8,
    mut v_h_393_: *mut leanh::LeanObject,
    mut v_ce_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ce_394_);
    return v_ce_394_;
}
pub unsafe fn l_Std_Time_Year_Era_ce_elim___boxed(
    mut v_motive_395_: *mut leanh::LeanObject,
    mut v_t_396_: *mut leanh::LeanObject,
    mut v_h_397_: *mut leanh::LeanObject,
    mut v_ce_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_399_: u8 = 0;
    let mut v_res_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_399_ = (leanh::lean_unbox(v_t_396_) as u8);
    v_res_400_ = l_Std_Time_Year_Era_ce_elim(v_motive_395_, v_t_boxed_399_, v_h_397_, v_ce_398_);
    leanh::lean_dec(v_ce_398_);
    return v_res_400_;
}
pub unsafe fn _init_l_Std_Time_Year_instReprEra_repr___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_unsigned_to_nat(2);
    v___x_408_ = lean_nat_to_int(v___x_407_);
    return v___x_408_;
}
pub unsafe fn _init_l_Std_Time_Year_instReprEra_repr___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = leanh::lean_unsigned_to_nat(1);
    v___x_410_ = lean_nat_to_int(v___x_409_);
    return v___x_410_;
}
pub unsafe fn l_Std_Time_Year_instReprEra_repr(
    mut v_x_411_: u8,
    mut v_prec_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: u8 = 0;
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: u8 = 0;
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_411_ == 0 {
                    v___x_427_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_428_ = lean_nat_dec_le(v___x_427_, v_prec_412_);
                    if v___x_428_ == 0 {
                        v___x_429_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_Year_instReprEra_repr___closed__4_once
                            ),
                            _init_l_Std_Time_Year_instReprEra_repr___closed__4,
                        );
                        v___y_414_ = v___x_429_;
                        state = 1;
                        continue;
                    } else {
                        v___x_430_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_Year_instReprEra_repr___closed__5_once
                            ),
                            _init_l_Std_Time_Year_instReprEra_repr___closed__5,
                        );
                        v___y_414_ = v___x_430_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_431_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_432_ = lean_nat_dec_le(v___x_431_, v_prec_412_);
                    if v___x_432_ == 0 {
                        v___x_433_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_Year_instReprEra_repr___closed__4_once
                            ),
                            _init_l_Std_Time_Year_instReprEra_repr___closed__4,
                        );
                        v___y_421_ = v___x_433_;
                        state = 2;
                        continue;
                    } else {
                        v___x_434_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_Year_instReprEra_repr___closed__5_once
                            ),
                            _init_l_Std_Time_Year_instReprEra_repr___closed__5,
                        );
                        v___y_421_ = v___x_434_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_415_ = l_Std_Time_Year_instReprEra_repr___closed__1;
                leanh::lean_inc(v___y_414_);
                v___x_416_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_416_, 0, v___y_414_);
                leanh::lean_ctor_set(v___x_416_, 1, v___x_415_);
                v___x_417_ = 0;
                v___x_418_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_418_, 0, v___x_416_);
                leanh::lean_ctor_set_uint8(
                    v___x_418_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_417_,
                );
                v___x_419_ = l_Repr_addAppParen(v___x_418_, v_prec_412_);
                return v___x_419_;
            }
            2 => {
                v___x_422_ = l_Std_Time_Year_instReprEra_repr___closed__3;
                leanh::lean_inc(v___y_421_);
                v___x_423_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_423_, 0, v___y_421_);
                leanh::lean_ctor_set(v___x_423_, 1, v___x_422_);
                v___x_424_ = 0;
                v___x_425_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_425_, 0, v___x_423_);
                leanh::lean_ctor_set_uint8(
                    v___x_425_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_424_,
                );
                v___x_426_ = l_Repr_addAppParen(v___x_425_, v_prec_412_);
                return v___x_426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Year_instReprEra_repr___boxed(
    mut v_x_435_: *mut leanh::LeanObject,
    mut v_prec_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_121__boxed_437_: u8 = 0;
    let mut v_res_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_121__boxed_437_ = (leanh::lean_unbox(v_x_435_) as u8);
    v_res_438_ = l_Std_Time_Year_instReprEra_repr(v_x_121__boxed_437_, v_prec_436_);
    leanh::lean_dec(v_prec_436_);
    return v_res_438_;
}
pub unsafe fn _init_l_Std_Time_Year_instInhabitedEra_default() -> u8 {
    let mut v___x_441_: u8 = 0;
    v___x_441_ = 0;
    return v___x_441_;
}
pub unsafe fn _init_l_Std_Time_Year_instInhabitedEra() -> u8 {
    let mut v___x_442_: u8 = 0;
    v___x_442_ = 0;
    return v___x_442_;
}
pub unsafe fn l_Std_Time_Year_instToStringEra___lam__0(
    mut v_x_445_: u8,
) -> *mut leanh::LeanObject {
    if v_x_445_ == 0 {
        let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_446_ = l_Std_Time_Year_instToStringEra___lam__0___closed__0;
        return v___x_446_;
    } else {
        let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_447_ = l_Std_Time_Year_instToStringEra___lam__0___closed__1;
        return v___x_447_;
    }
}
pub unsafe fn l_Std_Time_Year_instToStringEra___lam__0___boxed(
    mut v_x_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_449_: u8 = 0;
    let mut v_res_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_449_ = (leanh::lean_unbox(v_x_448_) as u8);
    v_res_450_ = l_Std_Time_Year_instToStringEra___lam__0(v_x_26__boxed_449_);
    return v_res_450_;
}
pub unsafe fn _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = leanh::lean_unsigned_to_nat(0);
    v___x_454_ = lean_nat_to_int(v___x_453_);
    return v___x_454_;
}
pub unsafe fn l_Std_Time_Year_instReprOffset___aux__1(
    mut v_i_455_: *mut leanh::LeanObject,
    mut v_prec_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    v___x_457_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
    );
    v___x_458_ = lean_int_dec_lt(v_i_455_, v___x_457_);
    if v___x_458_ == 0 {
        let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_459_ = l_Int_repr(v_i_455_);
        v___x_460_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_460_, 0, v___x_459_);
        return v___x_460_;
    } else {
        let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_461_ = l_Int_repr(v_i_455_);
        v___x_462_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_462_, 0, v___x_461_);
        v___x_463_ = l_Repr_addAppParen(v___x_462_, v_prec_456_);
        return v___x_463_;
    }
}
pub unsafe fn l_Std_Time_Year_instReprOffset___aux__1___boxed(
    mut v_i_464_: *mut leanh::LeanObject,
    mut v_prec_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_466_ = l_Std_Time_Year_instReprOffset___aux__1(v_i_464_, v_prec_465_);
    leanh::lean_dec(v_prec_465_);
    leanh::lean_dec(v_i_464_);
    return v_res_466_;
}
pub unsafe fn l_Std_Time_Year_instReprOffset___lam__0(
    mut v___y_467_: *mut leanh::LeanObject,
    mut v___y_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: u8 = 0;
    v___x_469_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
    );
    v___x_470_ = lean_int_dec_lt(v___y_467_, v___x_469_);
    if v___x_470_ == 0 {
        let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_471_ = l_Int_repr(v___y_467_);
        v___x_472_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_472_, 0, v___x_471_);
        return v___x_472_;
    } else {
        let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_473_ = l_Int_repr(v___y_467_);
        v___x_474_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_474_, 0, v___x_473_);
        v___x_475_ = l_Repr_addAppParen(v___x_474_, v___y_468_);
        return v___x_475_;
    }
}
pub unsafe fn l_Std_Time_Year_instReprOffset___lam__0___boxed(
    mut v___y_476_: *mut leanh::LeanObject,
    mut v___y_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Time_Year_instReprOffset___lam__0(v___y_476_, v___y_477_);
    leanh::lean_dec(v___y_477_);
    leanh::lean_dec(v___y_476_);
    return v_res_478_;
}
pub unsafe fn l_Std_Time_Year_instDecidableEqOffset___aux__1(
    mut v_a_481_: *mut leanh::LeanObject,
    mut v_b_482_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_483_: u8 = 0;
    v___x_483_ = lean_int_dec_eq(v_a_481_, v_b_482_);
    return v___x_483_;
}
pub unsafe fn l_Std_Time_Year_instDecidableEqOffset___aux__1___boxed(
    mut v_a_484_: *mut leanh::LeanObject,
    mut v_b_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_486_: u8 = 0;
    let mut v_r_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_486_ = l_Std_Time_Year_instDecidableEqOffset___aux__1(v_a_484_, v_b_485_);
    leanh::lean_dec(v_b_485_);
    leanh::lean_dec(v_a_484_);
    v_r_487_ = leanh::lean_box((v_res_486_) as usize);
    return v_r_487_;
}
pub unsafe fn l_Std_Time_Year_instDecidableEqOffset(
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_b_489_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_490_: u8 = 0;
    v___x_490_ = lean_int_dec_eq(v_a_488_, v_b_489_);
    return v___x_490_;
}
pub unsafe fn l_Std_Time_Year_instDecidableEqOffset___boxed(
    mut v_a_491_: *mut leanh::LeanObject,
    mut v_b_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = l_Std_Time_Year_instDecidableEqOffset(v_a_491_, v_b_492_);
    leanh::lean_dec(v_b_492_);
    leanh::lean_dec(v_a_491_);
    v_r_494_ = leanh::lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn _init_l_Std_Time_Year_instInhabitedOffset___aux__1() -> *mut leanh::LeanObject
{
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_495_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
    );
    return v___x_495_;
}
pub unsafe fn _init_l_Std_Time_Year_instInhabitedOffset() -> *mut leanh::LeanObject {
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
    );
    return v___x_496_;
}
pub unsafe fn l_Std_Time_Year_instAddOffset___aux__1(
    mut v_m_497_: *mut leanh::LeanObject,
    mut v_n_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_int_add(v_m_497_, v_n_498_);
    return v___x_499_;
}
pub unsafe fn l_Std_Time_Year_instAddOffset___aux__1___boxed(
    mut v_m_500_: *mut leanh::LeanObject,
    mut v_n_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Std_Time_Year_instAddOffset___aux__1(v_m_500_, v_n_501_);
    leanh::lean_dec(v_n_501_);
    leanh::lean_dec(v_m_500_);
    return v_res_502_;
}
pub unsafe fn l_Std_Time_Year_instSubOffset___aux__1(
    mut v_m_505_: *mut leanh::LeanObject,
    mut v_n_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_507_ = lean_int_sub(v_m_505_, v_n_506_);
    return v___x_507_;
}
pub unsafe fn l_Std_Time_Year_instSubOffset___aux__1___boxed(
    mut v_m_508_: *mut leanh::LeanObject,
    mut v_n_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_510_ = l_Std_Time_Year_instSubOffset___aux__1(v_m_508_, v_n_509_);
    leanh::lean_dec(v_n_509_);
    leanh::lean_dec(v_m_508_);
    return v_res_510_;
}
pub unsafe fn l_Std_Time_Year_instNegOffset___aux__1(
    mut v_n_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = lean_int_neg(v_n_513_);
    return v___x_514_;
}
pub unsafe fn l_Std_Time_Year_instNegOffset___aux__1___boxed(
    mut v_n_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Std_Time_Year_instNegOffset___aux__1(v_n_515_);
    leanh::lean_dec(v_n_515_);
    return v_res_516_;
}
pub unsafe fn _init_l_Std_Time_Year_instLEOffset() -> *mut leanh::LeanObject {
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_519_ = leanh::lean_box(0);
    return v___x_519_;
}
pub unsafe fn _init_l_Std_Time_Year_instLTOffset() -> *mut leanh::LeanObject {
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_520_ = leanh::lean_box(0);
    return v___x_520_;
}
pub unsafe fn l_Std_Time_Year_instToStringOffset___aux__1(
    mut v_a_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = l_Int_repr(v_a_521_);
    return v___x_522_;
}
pub unsafe fn l_Std_Time_Year_instToStringOffset___aux__1___boxed(
    mut v_a_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_Time_Year_instToStringOffset___aux__1(v_a_523_);
    leanh::lean_dec(v_a_523_);
    return v_res_524_;
}
pub unsafe fn l_Std_Time_Year_instDecidableLeOffset(
    mut v_x_527_: *mut leanh::LeanObject,
    mut v_y_528_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_529_: u8 = 0;
    v___x_529_ = lean_int_dec_le(v_x_527_, v_y_528_);
    return v___x_529_;
}
pub unsafe fn l_Std_Time_Year_instDecidableLeOffset___boxed(
    mut v_x_530_: *mut leanh::LeanObject,
    mut v_y_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_532_: u8 = 0;
    let mut v_r_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Std_Time_Year_instDecidableLeOffset(v_x_530_, v_y_531_);
    leanh::lean_dec(v_y_531_);
    leanh::lean_dec(v_x_530_);
    v_r_533_ = leanh::lean_box((v_res_532_) as usize);
    return v_r_533_;
}
pub unsafe fn l_Std_Time_Year_instDecidableLtOffset(
    mut v_x_534_: *mut leanh::LeanObject,
    mut v_y_535_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_536_: u8 = 0;
    v___x_536_ = lean_int_dec_lt(v_x_534_, v_y_535_);
    return v___x_536_;
}
pub unsafe fn l_Std_Time_Year_instDecidableLtOffset___boxed(
    mut v_x_537_: *mut leanh::LeanObject,
    mut v_y_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_539_: u8 = 0;
    let mut v_r_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_539_ = l_Std_Time_Year_instDecidableLtOffset(v_x_537_, v_y_538_);
    leanh::lean_dec(v_y_538_);
    leanh::lean_dec(v_x_537_);
    v_r_540_ = leanh::lean_box((v_res_539_) as usize);
    return v_r_540_;
}
pub unsafe fn l_Std_Time_Year_instOfNatOffset(
    mut v_n_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ = lean_nat_to_int(v_n_541_);
    return v___x_542_;
}
pub unsafe fn l_Std_Time_Year_instOrdOffset___aux__1(
    mut v_x_543_: *mut leanh::LeanObject,
    mut v_y_544_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_545_: u8 = 0;
    v___x_545_ = lean_int_dec_lt(v_x_543_, v_y_544_);
    if v___x_545_ == 0 {
        let mut v___x_546_: u8 = 0;
        v___x_546_ = lean_int_dec_eq(v_x_543_, v_y_544_);
        if v___x_546_ == 0 {
            let mut v___x_547_: u8 = 0;
            v___x_547_ = 2;
            return v___x_547_;
        } else {
            let mut v___x_548_: u8 = 0;
            v___x_548_ = 1;
            return v___x_548_;
        }
    } else {
        let mut v___x_549_: u8 = 0;
        v___x_549_ = 0;
        return v___x_549_;
    }
}
pub unsafe fn l_Std_Time_Year_instOrdOffset___aux__1___boxed(
    mut v_x_550_: *mut leanh::LeanObject,
    mut v_y_551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_552_: u8 = 0;
    let mut v_r_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_552_ = l_Std_Time_Year_instOrdOffset___aux__1(v_x_550_, v_y_551_);
    leanh::lean_dec(v_y_551_);
    leanh::lean_dec(v_x_550_);
    v_r_553_ = leanh::lean_box((v_res_552_) as usize);
    return v_r_553_;
}
pub unsafe fn l_Std_Time_Year_Offset_ofNat(
    mut v_data_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = lean_nat_to_int(v_data_556_);
    return v___x_557_;
}
pub unsafe fn l_Std_Time_Year_Offset_ofInt(
    mut v_data_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_558_);
    return v_data_558_;
}
pub unsafe fn l_Std_Time_Year_Offset_ofInt___boxed(
    mut v_data_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Std_Time_Year_Offset_ofInt(v_data_559_);
    leanh::lean_dec(v_data_559_);
    return v_res_560_;
}
pub unsafe fn l_Std_Time_Year_Offset_toInt(
    mut v_offset_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_offset_561_);
    return v_offset_561_;
}
pub unsafe fn l_Std_Time_Year_Offset_toInt___boxed(
    mut v_offset_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_Std_Time_Year_Offset_toInt(v_offset_562_);
    leanh::lean_dec(v_offset_562_);
    return v_res_563_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_toMonths___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = leanh::lean_unsigned_to_nat(12);
    v___x_565_ = lean_nat_to_int(v___x_564_);
    return v___x_565_;
}
pub unsafe fn l_Std_Time_Year_Offset_toMonths(
    mut v_val_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_toMonths___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_toMonths___closed__0_once),
        _init_l_Std_Time_Year_Offset_toMonths___closed__0,
    );
    v___x_568_ = lean_int_mul(v_val_566_, v___x_567_);
    return v___x_568_;
}
pub unsafe fn l_Std_Time_Year_Offset_toMonths___boxed(
    mut v_val_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_570_ = l_Std_Time_Year_Offset_toMonths(v_val_569_);
    leanh::lean_dec(v_val_569_);
    return v_res_570_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_isLeap___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = leanh::lean_unsigned_to_nat(4);
    v___x_572_ = lean_nat_to_int(v___x_571_);
    return v___x_572_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_isLeap___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = leanh::lean_unsigned_to_nat(400);
    v___x_574_ = lean_nat_to_int(v___x_573_);
    return v___x_574_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_isLeap___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_575_ = leanh::lean_unsigned_to_nat(100);
    v___x_576_ = lean_nat_to_int(v___x_575_);
    return v___x_576_;
}
pub unsafe fn l_Std_Time_Year_Offset_isLeap(mut v_y_577_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_578_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0_once),
                    _init_l_Std_Time_Year_Offset_isLeap___closed__0,
                );
                v___x_579_ = lean_int_mod(v_y_577_, v___x_578_);
                v___x_580_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_Year_instReprOffset___aux__1___closed__0_once
                    ),
                    _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
                );
                v___x_585_ = lean_int_dec_eq(v___x_579_, v___x_580_);
                leanh::lean_dec(v___x_579_);
                if v___x_585_ == 0 {
                    return v___x_585_;
                } else {
                    v___x_586_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__2_once),
                        _init_l_Std_Time_Year_Offset_isLeap___closed__2,
                    );
                    v___x_587_ = lean_int_mod(v_y_577_, v___x_586_);
                    v___x_588_ = lean_int_dec_eq(v___x_587_, v___x_580_);
                    leanh::lean_dec(v___x_587_);
                    if v___x_588_ == 0 {
                        if v___x_585_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_585_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_582_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__1_once),
                    _init_l_Std_Time_Year_Offset_isLeap___closed__1,
                );
                v___x_583_ = lean_int_mod(v_y_577_, v___x_582_);
                v___x_584_ = lean_int_dec_eq(v___x_583_, v___x_580_);
                leanh::lean_dec(v___x_583_);
                return v___x_584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Year_Offset_isLeap___boxed(
    mut v_y_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: u8 = 0;
    let mut v_r_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Std_Time_Year_Offset_isLeap(v_y_589_);
    leanh::lean_dec(v_y_589_);
    v_r_591_ = leanh::lean_box((v_res_590_) as usize);
    return v_r_591_;
}
pub unsafe fn l_Std_Time_Year_Offset_era(mut v_year_592_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: u8 = 0;
    v___x_593_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5_once),
        _init_l_Std_Time_Year_instReprEra_repr___closed__5,
    );
    v___x_594_ = lean_int_dec_le(v___x_593_, v_year_592_);
    if v___x_594_ == 0 {
        let mut v___x_595_: u8 = 0;
        v___x_595_ = 0;
        return v___x_595_;
    } else {
        let mut v___x_596_: u8 = 0;
        v___x_596_ = 1;
        return v___x_596_;
    }
}
pub unsafe fn l_Std_Time_Year_Offset_era___boxed(
    mut v_year_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_598_: u8 = 0;
    let mut v_r_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Std_Time_Year_Offset_era(v_year_597_);
    leanh::lean_dec(v_year_597_);
    v_r_599_ = leanh::lean_box((v_res_598_) as usize);
    return v_r_599_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = leanh::lean_unsigned_to_nat(365);
    v___x_601_ = lean_nat_to_int(v___x_600_);
    return v___x_601_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = leanh::lean_unsigned_to_nat(366);
    v___x_603_ = lean_nat_to_int(v___x_602_);
    return v___x_603_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_604_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0_once),
        _init_l_Std_Time_Year_Offset_days___closed__0,
    );
    v___x_605_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__1_once),
        _init_l_Std_Time_Year_Offset_days___closed__1,
    );
    v___x_606_ = lean_int_sub(v___x_605_, v___x_604_);
    return v___x_606_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5_once),
        _init_l_Std_Time_Year_instReprEra_repr___closed__5,
    );
    v___x_608_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__2_once),
        _init_l_Std_Time_Year_Offset_days___closed__2,
    );
    v_range_609_ = lean_int_add(v___x_608_, v___x_607_);
    return v_range_609_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__4() -> *mut leanh::LeanObject {
    let mut v_range_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_610_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3_once),
        _init_l_Std_Time_Year_Offset_days___closed__3,
    );
    v___x_611_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__2_once),
        _init_l_Std_Time_Year_Offset_days___closed__2,
    );
    v___x_612_ = lean_int_emod(v___x_611_, v_range_610_);
    return v___x_612_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__5() -> *mut leanh::LeanObject {
    let mut v_range_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_613_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3_once),
        _init_l_Std_Time_Year_Offset_days___closed__3,
    );
    v___x_614_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__4_once),
        _init_l_Std_Time_Year_Offset_days___closed__4,
    );
    v___x_615_ = lean_int_add(v___x_614_, v_range_613_);
    return v___x_615_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__6() -> *mut leanh::LeanObject {
    let mut v_range_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_616_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3_once),
        _init_l_Std_Time_Year_Offset_days___closed__3,
    );
    v___x_617_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__5_once),
        _init_l_Std_Time_Year_Offset_days___closed__5,
    );
    v___x_618_ = lean_int_emod(v___x_617_, v_range_616_);
    return v___x_618_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_619_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0_once),
        _init_l_Std_Time_Year_Offset_days___closed__0,
    );
    v___x_620_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__6_once),
        _init_l_Std_Time_Year_Offset_days___closed__6,
    );
    v___x_621_ = lean_int_add(v___x_620_, v___x_619_);
    return v___x_621_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = leanh::lean_unsigned_to_nat(355);
    v___x_623_ = lean_nat_to_int(v___x_622_);
    return v___x_623_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0_once),
        _init_l_Std_Time_Year_Offset_days___closed__0,
    );
    v___x_625_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__8_once),
        _init_l_Std_Time_Year_Offset_days___closed__8,
    );
    v___x_626_ = lean_int_sub(v___x_625_, v___x_624_);
    return v___x_626_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__10() -> *mut leanh::LeanObject {
    let mut v_range_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_627_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3_once),
        _init_l_Std_Time_Year_Offset_days___closed__3,
    );
    v___x_628_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__9_once),
        _init_l_Std_Time_Year_Offset_days___closed__9,
    );
    v___x_629_ = lean_int_emod(v___x_628_, v_range_627_);
    return v___x_629_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__11() -> *mut leanh::LeanObject {
    let mut v_range_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_630_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3_once),
        _init_l_Std_Time_Year_Offset_days___closed__3,
    );
    v___x_631_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__10_once),
        _init_l_Std_Time_Year_Offset_days___closed__10,
    );
    v___x_632_ = lean_int_add(v___x_631_, v_range_630_);
    return v___x_632_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__12() -> *mut leanh::LeanObject {
    let mut v_range_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_633_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__3_once),
        _init_l_Std_Time_Year_Offset_days___closed__3,
    );
    v___x_634_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__11_once),
        _init_l_Std_Time_Year_Offset_days___closed__11,
    );
    v___x_635_ = lean_int_emod(v___x_634_, v_range_633_);
    return v___x_635_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_days___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__0_once),
        _init_l_Std_Time_Year_Offset_days___closed__0,
    );
    v___x_637_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__12_once),
        _init_l_Std_Time_Year_Offset_days___closed__12,
    );
    v___x_638_ = lean_int_add(v___x_637_, v___x_636_);
    return v___x_638_;
}
pub unsafe fn l_Std_Time_Year_Offset_days(
    mut v_year_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0_once),
                    _init_l_Std_Time_Year_Offset_isLeap___closed__0,
                );
                v___x_645_ = lean_int_mod(v_year_639_, v___x_644_);
                v___x_646_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_instReprOffset___aux__1___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_Year_instReprOffset___aux__1___closed__0_once
                    ),
                    _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
                );
                v___x_651_ = lean_int_dec_eq(v___x_645_, v___x_646_);
                leanh::lean_dec(v___x_645_);
                if v___x_651_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_652_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__2_once),
                        _init_l_Std_Time_Year_Offset_isLeap___closed__2,
                    );
                    v___x_653_ = lean_int_mod(v_year_639_, v___x_652_);
                    v___x_654_ = lean_int_dec_eq(v___x_653_, v___x_646_);
                    leanh::lean_dec(v___x_653_);
                    if v___x_654_ == 0 {
                        if v___x_651_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_641_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__7_once),
                    _init_l_Std_Time_Year_Offset_days___closed__7,
                );
                return v___x_641_;
            }
            2 => {
                v___x_643_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__13),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_days___closed__13_once),
                    _init_l_Std_Time_Year_Offset_days___closed__13,
                );
                return v___x_643_;
            }
            3 => {
                v___x_648_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__1_once),
                    _init_l_Std_Time_Year_Offset_isLeap___closed__1,
                );
                v___x_649_ = lean_int_mod(v_year_639_, v___x_648_);
                v___x_650_ = lean_int_dec_eq(v___x_649_, v___x_646_);
                leanh::lean_dec(v___x_649_);
                if v___x_650_ == 0 {
                    state = 2;
                    continue;
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Year_Offset_days___boxed(
    mut v_year_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Std_Time_Year_Offset_days(v_year_655_);
    leanh::lean_dec(v_year_655_);
    return v_res_656_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Year_Offset_weeks_spec__0(
    mut v_a_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = lean_nat_to_int(v_a_657_);
    return v___x_658_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_weeks___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = leanh::lean_unsigned_to_nat(7);
    v___x_660_ = lean_nat_to_int(v___x_659_);
    return v___x_660_;
}
pub unsafe fn l_Std_Time_Year_Offset_weeks___lam__0(
    mut v_year_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0_once),
        _init_l_Std_Time_Year_Offset_isLeap___closed__0,
    );
    v___x_663_ = lean_int_ediv(v_year_661_, v___x_662_);
    v___x_664_ = lean_int_add(v_year_661_, v___x_663_);
    leanh::lean_dec(v___x_663_);
    v___x_665_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__2_once),
        _init_l_Std_Time_Year_Offset_isLeap___closed__2,
    );
    v___x_666_ = lean_int_ediv(v_year_661_, v___x_665_);
    v___x_667_ = lean_int_sub(v___x_664_, v___x_666_);
    leanh::lean_dec(v___x_666_);
    leanh::lean_dec(v___x_664_);
    v___x_668_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__1_once),
        _init_l_Std_Time_Year_Offset_isLeap___closed__1,
    );
    v___x_669_ = lean_int_ediv(v_year_661_, v___x_668_);
    v___x_670_ = lean_int_add(v___x_667_, v___x_669_);
    leanh::lean_dec(v___x_669_);
    leanh::lean_dec(v___x_667_);
    v___x_671_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_weeks___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_weeks___lam__0___closed__0_once),
        _init_l_Std_Time_Year_Offset_weeks___lam__0___closed__0,
    );
    v___x_672_ = lean_int_emod(v___x_670_, v___x_671_);
    leanh::lean_dec(v___x_670_);
    return v___x_672_;
}
pub unsafe fn l_Std_Time_Year_Offset_weeks___lam__0___boxed(
    mut v_year_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Std_Time_Year_Offset_weeks___lam__0(v_year_673_);
    leanh::lean_dec(v_year_673_);
    return v_res_674_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_weeks___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = leanh::lean_unsigned_to_nat(52);
    v___x_676_ = lean_nat_to_int(v___x_675_);
    return v___x_676_;
}
pub unsafe fn _init_l_Std_Time_Year_Offset_weeks___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = leanh::lean_unsigned_to_nat(3);
    v___x_678_ = lean_nat_to_int(v___x_677_);
    return v___x_678_;
}
pub unsafe fn l_Std_Time_Year_Offset_weeks(
    mut v_year_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_686_ = l_Std_Time_Year_Offset_weeks___lam__0(v_year_679_);
                v___x_687_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_isLeap___closed__0_once),
                    _init_l_Std_Time_Year_Offset_isLeap___closed__0,
                );
                v___x_688_ = lean_int_dec_eq(v___x_686_, v___x_687_);
                leanh::lean_dec(v___x_686_);
                if v___x_688_ == 0 {
                    v___x_689_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5),
                        core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5_once),
                        _init_l_Std_Time_Year_instReprEra_repr___closed__5,
                    );
                    v___x_690_ = lean_int_sub(v_year_679_, v___x_689_);
                    v___x_691_ = l_Std_Time_Year_Offset_weeks___lam__0(v___x_690_);
                    leanh::lean_dec(v___x_690_);
                    v___x_692_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_weeks___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_weeks___closed__1_once),
                        _init_l_Std_Time_Year_Offset_weeks___closed__1,
                    );
                    v___x_693_ = lean_int_dec_eq(v___x_691_, v___x_692_);
                    leanh::lean_dec(v___x_691_);
                    if v___x_693_ == 0 {
                        v___x_694_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_Year_instReprOffset___aux__1___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_Year_instReprOffset___aux__1___closed__0_once
                            ),
                            _init_l_Std_Time_Year_instReprOffset___aux__1___closed__0,
                        );
                        v___y_681_ = v___x_694_;
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_682_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_weeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_Offset_weeks___closed__0_once),
                    _init_l_Std_Time_Year_Offset_weeks___closed__0,
                );
                v___x_683_ = lean_int_add(v___x_682_, v___y_681_);
                return v___x_683_;
            }
            2 => {
                v___x_685_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Time_Year_instReprEra_repr___closed__5_once),
                    _init_l_Std_Time_Year_instReprEra_repr___closed__5,
                );
                v___y_681_ = v___x_685_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Year_Offset_weeks___boxed(
    mut v_year_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Std_Time_Year_Offset_weeks(v_year_695_);
    leanh::lean_dec(v_year_695_);
    return v_res_696_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Year(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_Year_instInhabitedEra_default = _init_l_Std_Time_Year_instInhabitedEra_default();
    l_Std_Time_Year_instInhabitedEra = _init_l_Std_Time_Year_instInhabitedEra();
    l_Std_Time_Year_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Year_instInhabitedOffset___aux__1();
    leanh::lean_mark_persistent(l_Std_Time_Year_instInhabitedOffset___aux__1);
    l_Std_Time_Year_instInhabitedOffset = _init_l_Std_Time_Year_instInhabitedOffset();
    leanh::lean_mark_persistent(l_Std_Time_Year_instInhabitedOffset);
    l_Std_Time_Year_instLEOffset = _init_l_Std_Time_Year_instLEOffset();
    leanh::lean_mark_persistent(l_Std_Time_Year_instLEOffset);
    l_Std_Time_Year_instLTOffset = _init_l_Std_Time_Year_instLTOffset();
    leanh::lean_mark_persistent(l_Std_Time_Year_instLTOffset);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Year(
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
pub unsafe fn initialize_Std_Time_Date_Unit_Year(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Year(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Year(builtin);
}