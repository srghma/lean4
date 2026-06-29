// Lean compiler output
// Module: Std.Time.Date.Unit.Week
// Imports: Std.Time.Date.Unit.Day
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_instNatCast___lam__0, l_Rat_mul, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Std::Time::Date::Unit::Day::{
    initialize_Std_Time_Date_Unit_Day, runtime_initialize_Std_Time_Date_Unit_Day,
};
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_nat_dec_le};
static mut l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instReprOrdinal___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_instReprOrdinal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instReprOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instReprOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instLEOrdinal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Week_instLTOrdinal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_instInhabitedOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_instOrdOrdinal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instOrdOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instOrdOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instReprOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_instInhabitedOffset___aux__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_instInhabitedOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_instAddOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_instSubOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_instNegOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instNegOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instNegOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instLEOffset: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Week_instLTOffset: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Week_instToStringOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Week_instToStringOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instToStringOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_instOrdOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instOrdOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_instOrdOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_Ordinal_instReprOfMonth: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value:
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
    m_fun: l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Week_Ordinal_instOrdOfMonth: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value:
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
    m_data: [100, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14249328086033210933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_Ordinal_ofNat___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofFin___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_ofFin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Offset_toMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toNanoseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Offset_toNanoseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Offset_toSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Offset_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Offset_toHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toDays___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Offset_toDays___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_517_ = lean_nat_to_int(v___x_516_);
    return v___x_517_;
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___aux__1(
    mut v_n_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: u8 = 0;
    v___x_520_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_521_ = lean_int_dec_lt(v_n_518_, v___x_520_);
    if v___x_521_ == 0 {
        let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_522_ = l_Int_repr(v_n_518_);
        v___x_523_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_523_, 0, v___x_522_);
        return v___x_523_;
    } else {
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_524_ = l_Int_repr(v_n_518_);
        v___x_525_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_525_, 0, v___x_524_);
        v___x_526_ = l_Repr_addAppParen(v___x_525_, v_a_519_);
        return v___x_526_;
    }
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___aux__1___boxed(
    mut v_n_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Std_Time_Week_instReprOrdinal___aux__1(v_n_527_, v_a_528_);
    crate::leanh::lean_dec(v_a_528_);
    crate::leanh::lean_dec(v_n_527_);
    return v_res_529_;
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___lam__0(
    mut v___y_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    v___x_532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_533_ = lean_int_dec_lt(v___y_530_, v___x_532_);
    if v___x_533_ == 0 {
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_534_ = l_Int_repr(v___y_530_);
        v___x_535_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_535_, 0, v___x_534_);
        return v___x_535_;
    } else {
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_536_ = l_Int_repr(v___y_530_);
        v___x_537_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_537_, 0, v___x_536_);
        v___x_538_ = l_Repr_addAppParen(v___x_537_, v___y_531_);
        return v___x_538_;
    }
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___lam__0___boxed(
    mut v___y_539_: *mut crate::leanh::LeanObject,
    mut v___y_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_541_ = l_Std_Time_Week_instReprOrdinal___lam__0(v___y_539_, v___y_540_);
    crate::leanh::lean_dec(v___y_540_);
    crate::leanh::lean_dec(v___y_539_);
    return v_res_541_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal___aux__1(
    mut v_a_544_: *mut crate::leanh::LeanObject,
    mut v_b_545_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_546_: u8 = 0;
    v___x_546_ = lean_int_dec_eq(v_a_544_, v_b_545_);
    return v___x_546_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_b_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: u8 = 0;
    let mut v_r_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_a_547_, v_b_548_);
    crate::leanh::lean_dec(v_b_548_);
    crate::leanh::lean_dec(v_a_547_);
    v_r_550_ = crate::leanh::lean_box((v_res_549_) as usize);
    return v_r_550_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal(
    mut v_a_551_: *mut crate::leanh::LeanObject,
    mut v_b_552_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_553_: u8 = 0;
    v___x_553_ = lean_int_dec_eq(v_a_551_, v_b_552_);
    return v___x_553_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal___boxed(
    mut v_a_554_: *mut crate::leanh::LeanObject,
    mut v_b_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_556_: u8 = 0;
    let mut v_r_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_556_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_554_, v_b_555_);
    crate::leanh::lean_dec(v_b_555_);
    crate::leanh::lean_dec(v_a_554_);
    v_r_557_ = crate::leanh::lean_box((v_res_556_) as usize);
    return v_r_557_;
}
pub unsafe fn _init_l_Std_Time_Week_instLEOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = crate::leanh::lean_box(0);
    return v___x_558_;
}
pub unsafe fn _init_l_Std_Time_Week_instLTOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_559_ = crate::leanh::lean_box(0);
    return v___x_559_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_561_ = lean_nat_to_int(v___x_560_);
    return v___x_561_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = crate::leanh::lean_unsigned_to_nat(52);
    v___x_563_ = lean_nat_to_int(v___x_562_);
    return v___x_563_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_565_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_566_ = lean_int_add(v___x_565_, v___x_564_);
    return v___x_566_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_568_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2,
    );
    v___x_569_ = lean_int_sub(v___x_568_, v___x_567_);
    return v___x_569_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3,
    );
    v_range_572_ = lean_int_add(v___x_571_, v___x_570_);
    return v_range_572_;
}
pub unsafe fn l_Std_Time_Week_instOfNatOrdinal___aux__1(
    mut v_n_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_575_ = lean_nat_to_int(v_n_573_);
    v_range_576_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_577_ = lean_int_sub(v___x_575_, v___x_574_);
    crate::leanh::lean_dec(v___x_575_);
    v___x_578_ = lean_int_emod(v___x_577_, v_range_576_);
    crate::leanh::lean_dec(v___x_577_);
    v___x_579_ = lean_int_add(v___x_578_, v_range_576_);
    crate::leanh::lean_dec(v___x_578_);
    v___x_580_ = lean_int_emod(v___x_579_, v_range_576_);
    crate::leanh::lean_dec(v___x_579_);
    v___x_581_ = lean_int_add(v___x_580_, v___x_574_);
    crate::leanh::lean_dec(v___x_580_);
    return v___x_581_;
}
pub unsafe fn l_Std_Time_Week_instOfNatOrdinal(
    mut v_n_582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_584_ = lean_nat_to_int(v_n_582_);
    v_range_585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_586_ = lean_int_sub(v___x_584_, v___x_583_);
    crate::leanh::lean_dec(v___x_584_);
    v___x_587_ = lean_int_emod(v___x_586_, v_range_585_);
    crate::leanh::lean_dec(v___x_586_);
    v___x_588_ = lean_int_add(v___x_587_, v_range_585_);
    crate::leanh::lean_dec(v___x_587_);
    v___x_589_ = lean_int_emod(v___x_588_, v_range_585_);
    crate::leanh::lean_dec(v___x_588_);
    v___x_590_ = lean_int_add(v___x_589_, v___x_583_);
    crate::leanh::lean_dec(v___x_589_);
    return v___x_590_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal___aux__1(
    mut v_x_591_: *mut crate::leanh::LeanObject,
    mut v_y_592_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_593_: u8 = 0;
    v___x_593_ = lean_int_dec_le(v_x_591_, v_y_592_);
    return v___x_593_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_594_: *mut crate::leanh::LeanObject,
    mut v_y_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_596_: u8 = 0;
    let mut v_r_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Std_Time_Week_instDecidableLeOrdinal___aux__1(v_x_594_, v_y_595_);
    crate::leanh::lean_dec(v_y_595_);
    crate::leanh::lean_dec(v_x_594_);
    v_r_597_ = crate::leanh::lean_box((v_res_596_) as usize);
    return v_r_597_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal(
    mut v___y_598_: *mut crate::leanh::LeanObject,
    mut v___y_599_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_600_: u8 = 0;
    v___x_600_ = lean_int_dec_le(v___y_598_, v___y_599_);
    return v___x_600_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal___boxed(
    mut v___y_601_: *mut crate::leanh::LeanObject,
    mut v___y_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_603_: u8 = 0;
    let mut v_r_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Std_Time_Week_instDecidableLeOrdinal(v___y_601_, v___y_602_);
    crate::leanh::lean_dec(v___y_602_);
    crate::leanh::lean_dec(v___y_601_);
    v_r_604_ = crate::leanh::lean_box((v_res_603_) as usize);
    return v_r_604_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal___aux__1(
    mut v_x_605_: *mut crate::leanh::LeanObject,
    mut v_y_606_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_607_: u8 = 0;
    v___x_607_ = lean_int_dec_lt(v_x_605_, v_y_606_);
    return v___x_607_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_608_: *mut crate::leanh::LeanObject,
    mut v_y_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_610_: u8 = 0;
    let mut v_r_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_610_ = l_Std_Time_Week_instDecidableLtOrdinal___aux__1(v_x_608_, v_y_609_);
    crate::leanh::lean_dec(v_y_609_);
    crate::leanh::lean_dec(v_x_608_);
    v_r_611_ = crate::leanh::lean_box((v_res_610_) as usize);
    return v_r_611_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal(
    mut v___y_612_: *mut crate::leanh::LeanObject,
    mut v___y_613_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_614_: u8 = 0;
    v___x_614_ = lean_int_dec_lt(v___y_612_, v___y_613_);
    return v___x_614_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal___boxed(
    mut v___y_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_617_: u8 = 0;
    let mut v_r_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Std_Time_Week_instDecidableLtOrdinal(v___y_615_, v___y_616_);
    crate::leanh::lean_dec(v___y_616_);
    crate::leanh::lean_dec(v___y_615_);
    v_r_618_ = crate::leanh::lean_box((v_res_617_) as usize);
    return v_r_618_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_619_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_620_ = lean_int_sub(v___x_619_, v___x_619_);
    return v___x_620_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_range_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_621_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_622_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0,
    );
    v___x_623_ = lean_int_emod(v___x_622_, v_range_621_);
    return v___x_623_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_range_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_624_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_625_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1,
    );
    v___x_626_ = lean_int_add(v___x_625_, v_range_624_);
    return v___x_626_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_range_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_627_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_628_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2,
    );
    v___x_629_ = lean_int_emod(v___x_628_, v_range_627_);
    return v___x_629_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_631_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3,
    );
    v___x_632_ = lean_int_add(v___x_631_, v___x_630_);
    return v___x_632_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4,
    );
    return v___x_633_;
}
pub unsafe fn l_Std_Time_Week_instOrdOrdinal___aux__1(
    mut v_x_634_: *mut crate::leanh::LeanObject,
    mut v_y_635_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_636_: u8 = 0;
    v___x_636_ = lean_int_dec_lt(v_x_634_, v_y_635_);
    if v___x_636_ == 0 {
        let mut v___x_637_: u8 = 0;
        v___x_637_ = lean_int_dec_eq(v_x_634_, v_y_635_);
        if v___x_637_ == 0 {
            let mut v___x_638_: u8 = 0;
            v___x_638_ = 2;
            return v___x_638_;
        } else {
            let mut v___x_639_: u8 = 0;
            v___x_639_ = 1;
            return v___x_639_;
        }
    } else {
        let mut v___x_640_: u8 = 0;
        v___x_640_ = 0;
        return v___x_640_;
    }
}
pub unsafe fn l_Std_Time_Week_instOrdOrdinal___aux__1___boxed(
    mut v_x_641_: *mut crate::leanh::LeanObject,
    mut v_y_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_641_, v_y_642_);
    crate::leanh::lean_dec(v_y_642_);
    crate::leanh::lean_dec(v_x_641_);
    v_r_644_ = crate::leanh::lean_box((v_res_643_) as usize);
    return v_r_644_;
}
pub unsafe fn l_Std_Time_Week_instReprOffset___aux__1(
    mut v_x_647_: *mut crate::leanh::LeanObject,
    mut v_p_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    v___x_649_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_650_ = lean_int_dec_lt(v_x_647_, v___x_649_);
    if v___x_650_ == 0 {
        let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_651_ = l_Int_repr(v_x_647_);
        v___x_652_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_652_, 0, v___x_651_);
        return v___x_652_;
    } else {
        let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_653_ = l_Int_repr(v_x_647_);
        v___x_654_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_654_, 0, v___x_653_);
        v___x_655_ = l_Repr_addAppParen(v___x_654_, v_p_648_);
        return v___x_655_;
    }
}
pub unsafe fn l_Std_Time_Week_instReprOffset___aux__1___boxed(
    mut v_x_656_: *mut crate::leanh::LeanObject,
    mut v_p_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Std_Time_Week_instReprOffset___aux__1(v_x_656_, v_p_657_);
    crate::leanh::lean_dec(v_p_657_);
    crate::leanh::lean_dec(v_x_656_);
    return v_res_658_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset___aux__1(
    mut v_a_660_: *mut crate::leanh::LeanObject,
    mut v_b_661_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_662_: u8 = 0;
    v___x_662_ = lean_int_dec_eq(v_a_660_, v_b_661_);
    return v___x_662_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(
    mut v_a_663_: *mut crate::leanh::LeanObject,
    mut v_b_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_665_: u8 = 0;
    let mut v_r_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_a_663_, v_b_664_);
    crate::leanh::lean_dec(v_b_664_);
    crate::leanh::lean_dec(v_a_663_);
    v_r_666_ = crate::leanh::lean_box((v_res_665_) as usize);
    return v_r_666_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = lean_nat_to_int(v_a_667_);
    return v___x_668_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = lean_nat_to_int(v_a_669_);
    v___x_671_ = l_Rat_ofInt(v___x_670_);
    return v___x_671_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset(
    mut v_a_672_: *mut crate::leanh::LeanObject,
    mut v_b_673_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_674_: u8 = 0;
    v___x_674_ = lean_int_dec_eq(v_a_672_, v_b_673_);
    return v___x_674_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset___boxed(
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_b_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_677_: u8 = 0;
    let mut v_r_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Std_Time_Week_instDecidableEqOffset(v_a_675_, v_b_676_);
    crate::leanh::lean_dec(v_b_676_);
    crate::leanh::lean_dec(v_a_675_);
    v_r_678_ = crate::leanh::lean_box((v_res_677_) as usize);
    return v_r_678_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_680_ = l_Rat_instNatCast___lam__0(v___x_679_);
    return v___x_680_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_681_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_682_ = l_Rat_instNatCast___lam__0(v___x_681_);
    return v___x_682_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1,
    );
    v___x_684_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_685_ = l_Rat_mul(v___x_684_, v___x_683_);
    return v___x_685_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2,
    );
    v___x_687_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_686_);
    return v___x_687_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3,
    );
    return v___x_688_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_690_ =
        l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(v___x_689_);
    return v___x_690_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_692_ =
        l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(v___x_691_);
    return v___x_692_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__1,
    );
    v___x_694_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__0,
    );
    v___x_695_ = l_Rat_mul(v___x_694_, v___x_693_);
    return v___x_695_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__2_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__2,
    );
    v___x_697_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_696_);
    return v___x_697_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__3_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__3,
    );
    return v___x_698_;
}
pub unsafe fn l_Std_Time_Week_instAddOffset___aux__1(
    mut v_u1_699_: *mut crate::leanh::LeanObject,
    mut v_u2_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_701_ = lean_int_add(v_u1_699_, v_u2_700_);
    return v___x_701_;
}
pub unsafe fn l_Std_Time_Week_instAddOffset___aux__1___boxed(
    mut v_u1_702_: *mut crate::leanh::LeanObject,
    mut v_u2_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Std_Time_Week_instAddOffset___aux__1(v_u1_702_, v_u2_703_);
    crate::leanh::lean_dec(v_u2_703_);
    crate::leanh::lean_dec(v_u1_702_);
    return v_res_704_;
}
pub unsafe fn l_Std_Time_Week_instSubOffset___aux__1(
    mut v_u1_707_: *mut crate::leanh::LeanObject,
    mut v_u2_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_int_sub(v_u1_707_, v_u2_708_);
    return v___x_709_;
}
pub unsafe fn l_Std_Time_Week_instSubOffset___aux__1___boxed(
    mut v_u1_710_: *mut crate::leanh::LeanObject,
    mut v_u2_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Std_Time_Week_instSubOffset___aux__1(v_u1_710_, v_u2_711_);
    crate::leanh::lean_dec(v_u2_711_);
    crate::leanh::lean_dec(v_u1_710_);
    return v_res_712_;
}
pub unsafe fn l_Std_Time_Week_instNegOffset___aux__1(
    mut v_x_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = lean_int_neg(v_x_715_);
    return v___x_716_;
}
pub unsafe fn l_Std_Time_Week_instNegOffset___aux__1___boxed(
    mut v_x_717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Std_Time_Week_instNegOffset___aux__1(v_x_717_);
    crate::leanh::lean_dec(v_x_717_);
    return v_res_718_;
}
pub unsafe fn _init_l_Std_Time_Week_instLEOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = crate::leanh::lean_box(0);
    return v___x_721_;
}
pub unsafe fn _init_l_Std_Time_Week_instLTOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_722_ = crate::leanh::lean_box(0);
    return v___x_722_;
}
pub unsafe fn l_Std_Time_Week_instToStringOffset___aux__1(
    mut v_n_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Int_repr(v_n_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_Week_instToStringOffset___aux__1___boxed(
    mut v_n_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Std_Time_Week_instToStringOffset___aux__1(v_n_725_);
    crate::leanh::lean_dec(v_n_725_);
    return v_res_726_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset___aux__1(
    mut v_x_729_: *mut crate::leanh::LeanObject,
    mut v_y_730_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_731_: u8 = 0;
    v___x_731_ = lean_int_dec_le(v_x_729_, v_y_730_);
    return v___x_731_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(
    mut v_x_732_: *mut crate::leanh::LeanObject,
    mut v_y_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_734_: u8 = 0;
    let mut v_r_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_732_, v_y_733_);
    crate::leanh::lean_dec(v_y_733_);
    crate::leanh::lean_dec(v_x_732_);
    v_r_735_ = crate::leanh::lean_box((v_res_734_) as usize);
    return v_r_735_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset(
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_738_: u8 = 0;
    v___x_738_ = lean_int_dec_le(v___y_736_, v___y_737_);
    return v___x_738_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset___boxed(
    mut v___y_739_: *mut crate::leanh::LeanObject,
    mut v___y_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_741_: u8 = 0;
    let mut v_r_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Std_Time_Week_instDecidableLeOffset(v___y_739_, v___y_740_);
    crate::leanh::lean_dec(v___y_740_);
    crate::leanh::lean_dec(v___y_739_);
    v_r_742_ = crate::leanh::lean_box((v_res_741_) as usize);
    return v_r_742_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset___aux__1(
    mut v_x_743_: *mut crate::leanh::LeanObject,
    mut v_y_744_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_745_: u8 = 0;
    v___x_745_ = lean_int_dec_lt(v_x_743_, v_y_744_);
    return v___x_745_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(
    mut v_x_746_: *mut crate::leanh::LeanObject,
    mut v_y_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: u8 = 0;
    let mut v_r_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_746_, v_y_747_);
    crate::leanh::lean_dec(v_y_747_);
    crate::leanh::lean_dec(v_x_746_);
    v_r_749_ = crate::leanh::lean_box((v_res_748_) as usize);
    return v_r_749_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset(
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_752_: u8 = 0;
    v___x_752_ = lean_int_dec_lt(v___y_750_, v___y_751_);
    return v___x_752_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset___boxed(
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_755_: u8 = 0;
    let mut v_r_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_755_ = l_Std_Time_Week_instDecidableLtOffset(v___y_753_, v___y_754_);
    crate::leanh::lean_dec(v___y_754_);
    crate::leanh::lean_dec(v___y_753_);
    v_r_756_ = crate::leanh::lean_box((v_res_755_) as usize);
    return v_r_756_;
}
pub unsafe fn l_Std_Time_Week_instOfNatOffset(
    mut v_n_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_nat_to_int(v_n_757_);
    return v___x_758_;
}
pub unsafe fn l_Std_Time_Week_instOrdOffset___aux__1(
    mut v_x_759_: *mut crate::leanh::LeanObject,
    mut v_y_760_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_761_: u8 = 0;
    v___x_761_ = lean_int_dec_lt(v_x_759_, v_y_760_);
    if v___x_761_ == 0 {
        let mut v___x_762_: u8 = 0;
        v___x_762_ = lean_int_dec_eq(v_x_759_, v_y_760_);
        if v___x_762_ == 0 {
            let mut v___x_763_: u8 = 0;
            v___x_763_ = 2;
            return v___x_763_;
        } else {
            let mut v___x_764_: u8 = 0;
            v___x_764_ = 1;
            return v___x_764_;
        }
    } else {
        let mut v___x_765_: u8 = 0;
        v___x_765_ = 0;
        return v___x_765_;
    }
}
pub unsafe fn l_Std_Time_Week_instOrdOffset___aux__1___boxed(
    mut v_x_766_: *mut crate::leanh::LeanObject,
    mut v_y_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_768_: u8 = 0;
    let mut v_r_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_768_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_766_, v_y_767_);
    crate::leanh::lean_dec(v_y_767_);
    crate::leanh::lean_dec(v_x_766_);
    v_r_769_ = crate::leanh::lean_box((v_res_768_) as usize);
    return v_r_769_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt___redArg(
    mut v_data_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_772_);
    return v_data_772_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(
    mut v_data_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l_Std_Time_Week_Ordinal_ofInt___redArg(v_data_773_);
    crate::leanh::lean_dec(v_data_773_);
    return v_res_774_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt(
    mut v_data_775_: *mut crate::leanh::LeanObject,
    mut v_h_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_775_);
    return v_data_775_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt___boxed(
    mut v_data_777_: *mut crate::leanh::LeanObject,
    mut v_h_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_779_ = l_Std_Time_Week_Ordinal_ofInt(v_data_777_, v_h_778_);
    crate::leanh::lean_dec(v_data_777_);
    return v_res_779_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(
    mut v_n_780_: *mut crate::leanh::LeanObject,
    mut v_a_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    v___x_782_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_783_ = lean_int_dec_lt(v_n_780_, v___x_782_);
    if v___x_783_ == 0 {
        let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_784_ = l_Int_repr(v_n_780_);
        v___x_785_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_785_, 0, v___x_784_);
        return v___x_785_;
    } else {
        let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_786_ = l_Int_repr(v_n_780_);
        v___x_787_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_787_, 0, v___x_786_);
        v___x_788_ = l_Repr_addAppParen(v___x_787_, v_a_781_);
        return v___x_788_;
    }
}
pub unsafe fn l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1___boxed(
    mut v_n_789_: *mut crate::leanh::LeanObject,
    mut v_a_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(v_n_789_, v_a_790_);
    crate::leanh::lean_dec(v_a_790_);
    crate::leanh::lean_dec(v_n_789_);
    return v_res_791_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(
    mut v_a_793_: *mut crate::leanh::LeanObject,
    mut v_b_794_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_795_: u8 = 0;
    v___x_795_ = lean_int_dec_eq(v_a_793_, v_b_794_);
    return v___x_795_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1___boxed(
    mut v_a_796_: *mut crate::leanh::LeanObject,
    mut v_b_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: u8 = 0;
    let mut v_r_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(v_a_796_, v_b_797_);
    crate::leanh::lean_dec(v_b_797_);
    crate::leanh::lean_dec(v_a_796_);
    v_r_799_ = crate::leanh::lean_box((v_res_798_) as usize);
    return v_r_799_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_b_801_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_802_: u8 = 0;
    v___x_802_ = lean_int_dec_eq(v_a_800_, v_b_801_);
    return v___x_802_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v_b_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_805_: u8 = 0;
    let mut v_r_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(v_a_803_, v_b_804_);
    crate::leanh::lean_dec(v_b_804_);
    crate::leanh::lean_dec(v_a_803_);
    v_r_806_ = crate::leanh::lean_box((v_res_805_) as usize);
    return v_r_806_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_808_ = lean_nat_to_int(v___x_807_);
    return v___x_808_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0,
    );
    v___x_810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_811_ = lean_int_add(v___x_810_, v___x_809_);
    return v___x_811_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1,
    );
    v___x_814_ = lean_int_sub(v___x_813_, v___x_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2,
    );
    v_range_817_ = lean_int_add(v___x_816_, v___x_815_);
    return v_range_817_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1(
    mut v_n_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_820_ = lean_nat_to_int(v_n_818_);
    v_range_821_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_822_ = lean_int_sub(v___x_820_, v___x_819_);
    crate::leanh::lean_dec(v___x_820_);
    v___x_823_ = lean_int_emod(v___x_822_, v_range_821_);
    crate::leanh::lean_dec(v___x_822_);
    v___x_824_ = lean_int_add(v___x_823_, v_range_821_);
    crate::leanh::lean_dec(v___x_823_);
    v___x_825_ = lean_int_emod(v___x_824_, v_range_821_);
    crate::leanh::lean_dec(v___x_824_);
    v___x_826_ = lean_int_add(v___x_825_, v___x_819_);
    crate::leanh::lean_dec(v___x_825_);
    return v___x_826_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOfNatOfMonth(
    mut v_n_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_829_ = lean_nat_to_int(v_n_827_);
    v_range_830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_831_ = lean_int_sub(v___x_829_, v___x_828_);
    crate::leanh::lean_dec(v___x_829_);
    v___x_832_ = lean_int_emod(v___x_831_, v_range_830_);
    crate::leanh::lean_dec(v___x_831_);
    v___x_833_ = lean_int_add(v___x_832_, v_range_830_);
    crate::leanh::lean_dec(v___x_832_);
    v___x_834_ = lean_int_emod(v___x_833_, v_range_830_);
    crate::leanh::lean_dec(v___x_833_);
    v___x_835_ = lean_int_add(v___x_834_, v___x_828_);
    crate::leanh::lean_dec(v___x_834_);
    return v___x_835_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_range_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_836_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_837_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0,
    );
    v___x_838_ = lean_int_emod(v___x_837_, v_range_836_);
    return v___x_838_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_range_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_840_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0,
    );
    v___x_841_ = lean_int_add(v___x_840_, v_range_839_);
    return v___x_841_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_range_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_843_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1,
    );
    v___x_844_ = lean_int_emod(v___x_843_, v_range_842_);
    return v___x_844_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_845_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_846_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2,
    );
    v___x_847_ = lean_int_add(v___x_846_, v___x_845_);
    return v___x_847_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth() -> *mut crate::leanh::LeanObject
{
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3,
    );
    return v___x_848_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(
    mut v_x_849_: *mut crate::leanh::LeanObject,
    mut v_y_850_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_851_: u8 = 0;
    v___x_851_ = lean_int_dec_lt(v_x_849_, v_y_850_);
    if v___x_851_ == 0 {
        let mut v___x_852_: u8 = 0;
        v___x_852_ = lean_int_dec_eq(v_x_849_, v_y_850_);
        if v___x_852_ == 0 {
            let mut v___x_853_: u8 = 0;
            v___x_853_ = 2;
            return v___x_853_;
        } else {
            let mut v___x_854_: u8 = 0;
            v___x_854_ = 1;
            return v___x_854_;
        }
    } else {
        let mut v___x_855_: u8 = 0;
        v___x_855_ = 0;
        return v___x_855_;
    }
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed(
    mut v_x_856_: *mut crate::leanh::LeanObject,
    mut v_y_857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_858_: u8 = 0;
    let mut v_r_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_858_ = l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(v_x_856_, v_y_857_);
    crate::leanh::lean_dec(v_y_857_);
    crate::leanh::lean_dec(v_x_856_);
    v_r_859_ = crate::leanh::lean_box((v_res_858_) as usize);
    return v_r_859_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10;
    v___x_889_ = l_Lean_mkAtom(v___x_888_);
    return v___x_889_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12,
    );
    v___x_891_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_892_ = lean_array_push(v___x_891_, v___x_890_);
    return v___x_892_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16;
    v___x_904_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_905_ = lean_array_push(v___x_904_, v___x_903_);
    return v___x_905_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17,
    );
    v___x_907_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15;
    v___x_908_ = crate::leanh::lean_box(2);
    v___x_909_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_909_, 0, v___x_908_);
    crate::leanh::lean_ctor_set(v___x_909_, 1, v___x_907_);
    crate::leanh::lean_ctor_set(v___x_909_, 2, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18,
    );
    v___x_911_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13,
    );
    v___x_912_ = lean_array_push(v___x_911_, v___x_910_);
    return v___x_912_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19,
    );
    v___x_914_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11;
    v___x_915_ = crate::leanh::lean_box(2);
    v___x_916_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_916_, 0, v___x_915_);
    crate::leanh::lean_ctor_set(v___x_916_, 1, v___x_914_);
    crate::leanh::lean_ctor_set(v___x_916_, 2, v___x_913_);
    return v___x_916_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_917_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20,
    );
    v___x_918_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_919_ = lean_array_push(v___x_918_, v___x_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21,
    );
    v___x_921_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9;
    v___x_922_ = crate::leanh::lean_box(2);
    v___x_923_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
    crate::leanh::lean_ctor_set(v___x_923_, 1, v___x_921_);
    crate::leanh::lean_ctor_set(v___x_923_, 2, v___x_920_);
    return v___x_923_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22,
    );
    v___x_925_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_926_ = lean_array_push(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23,
    );
    v___x_928_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7;
    v___x_929_ = crate::leanh::lean_box(2);
    v___x_930_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_930_, 0, v___x_929_);
    crate::leanh::lean_ctor_set(v___x_930_, 1, v___x_928_);
    crate::leanh::lean_ctor_set(v___x_930_, 2, v___x_927_);
    return v___x_930_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24,
    );
    v___x_932_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_933_ = lean_array_push(v___x_932_, v___x_931_);
    return v___x_933_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25,
    );
    v___x_935_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4;
    v___x_936_ = crate::leanh::lean_box(2);
    v___x_937_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_937_, 0, v___x_936_);
    crate::leanh::lean_ctor_set(v___x_937_, 1, v___x_935_);
    crate::leanh::lean_ctor_set(v___x_937_, 2, v___x_934_);
    return v___x_937_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26,
    );
    return v___x_938_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofNat___redArg(
    mut v_data_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = lean_nat_to_int(v_data_939_);
    return v___x_940_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofNat(
    mut v_data_941_: *mut crate::leanh::LeanObject,
    mut v_h_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = lean_nat_to_int(v_data_941_);
    return v___x_943_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofFin___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_945_ = lean_nat_to_int(v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofFin(
    mut v_data_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    v___x_947_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_948_ = lean_nat_dec_le(v___x_947_, v_data_946_);
    if v___x_948_ == 0 {
        let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_data_946_);
        v___x_949_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofFin___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofFin___closed__0_once),
            _init_l_Std_Time_Week_Ordinal_ofFin___closed__0,
        );
        return v___x_949_;
    } else {
        let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_950_ = lean_nat_to_int(v_data_946_);
        return v___x_950_;
    }
}
pub unsafe fn l_Std_Time_Week_Ordinal_toOffset(
    mut v_ordinal_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ordinal_951_);
    return v_ordinal_951_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_toOffset___boxed(
    mut v_ordinal_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Std_Time_Week_Ordinal_toOffset(v_ordinal_952_);
    crate::leanh::lean_dec(v_ordinal_952_);
    return v_res_953_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofNat(
    mut v_data_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = lean_nat_to_int(v_data_954_);
    return v___x_955_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofInt(
    mut v_data_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_956_);
    return v_data_956_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofInt___boxed(
    mut v_data_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_958_ = l_Std_Time_Week_Offset_ofInt(v_data_957_);
    crate::leanh::lean_dec(v_data_957_);
    return v_res_958_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_959_ = crate::leanh::lean_unsigned_to_nat(604800000);
    v___x_960_ = lean_nat_to_int(v___x_959_);
    return v___x_960_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMilliseconds(
    mut v_weeks_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0,
    );
    v___x_963_ = lean_int_mul(v_weeks_961_, v___x_962_);
    return v___x_963_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMilliseconds___boxed(
    mut v_weeks_964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_965_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_964_);
    crate::leanh::lean_dec(v_weeks_964_);
    return v_res_965_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMilliseconds(
    mut v_millis_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0,
    );
    v___x_968_ = lean_int_ediv(v_millis_966_, v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMilliseconds___boxed(
    mut v_millis_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_969_);
    crate::leanh::lean_dec(v_millis_969_);
    return v_res_970_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_971_ = crate::leanh::lean_cstr_to_nat(b"604800000000000\0".as_ptr().cast());
    v___x_972_ = lean_nat_to_int(v___x_971_);
    return v___x_972_;
}
pub unsafe fn l_Std_Time_Week_Offset_toNanoseconds(
    mut v_weeks_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0,
    );
    v___x_975_ = lean_int_mul(v_weeks_973_, v___x_974_);
    return v___x_975_;
}
pub unsafe fn l_Std_Time_Week_Offset_toNanoseconds___boxed(
    mut v_weeks_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_977_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_976_);
    crate::leanh::lean_dec(v_weeks_976_);
    return v_res_977_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofNanoseconds(
    mut v_nanos_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0,
    );
    v___x_980_ = lean_int_ediv(v_nanos_978_, v___x_979_);
    return v___x_980_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofNanoseconds___boxed(
    mut v_nanos_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_981_);
    crate::leanh::lean_dec(v_nanos_981_);
    return v_res_982_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toSeconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = crate::leanh::lean_unsigned_to_nat(604800);
    v___x_984_ = lean_nat_to_int(v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Std_Time_Week_Offset_toSeconds(
    mut v_weeks_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toSeconds___closed__0,
    );
    v___x_987_ = lean_int_mul(v_weeks_985_, v___x_986_);
    return v___x_987_;
}
pub unsafe fn l_Std_Time_Week_Offset_toSeconds___boxed(
    mut v_weeks_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_988_);
    crate::leanh::lean_dec(v_weeks_988_);
    return v_res_989_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofSeconds(
    mut v_secs_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toSeconds___closed__0,
    );
    v___x_992_ = lean_int_ediv(v_secs_990_, v___x_991_);
    return v___x_992_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofSeconds___boxed(
    mut v_secs_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_993_);
    crate::leanh::lean_dec(v_secs_993_);
    return v_res_994_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toMinutes___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = crate::leanh::lean_unsigned_to_nat(10080);
    v___x_996_ = lean_nat_to_int(v___x_995_);
    return v___x_996_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMinutes(
    mut v_weeks_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMinutes___closed__0,
    );
    v___x_999_ = lean_int_mul(v_weeks_997_, v___x_998_);
    return v___x_999_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMinutes___boxed(
    mut v_weeks_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_1000_);
    crate::leanh::lean_dec(v_weeks_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMinutes(
    mut v_minutes_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMinutes___closed__0,
    );
    v___x_1004_ = lean_int_ediv(v_minutes_1002_, v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMinutes___boxed(
    mut v_minutes_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_1005_);
    crate::leanh::lean_dec(v_minutes_1005_);
    return v_res_1006_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toHours___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = crate::leanh::lean_unsigned_to_nat(168);
    v___x_1008_ = lean_nat_to_int(v___x_1007_);
    return v___x_1008_;
}
pub unsafe fn l_Std_Time_Week_Offset_toHours(
    mut v_weeks_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Week_Offset_toHours___closed__0,
    );
    v___x_1011_ = lean_int_mul(v_weeks_1009_, v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Std_Time_Week_Offset_toHours___boxed(
    mut v_weeks_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Std_Time_Week_Offset_toHours(v_weeks_1012_);
    crate::leanh::lean_dec(v_weeks_1012_);
    return v_res_1013_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofHours(
    mut v_hours_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Week_Offset_toHours___closed__0,
    );
    v___x_1016_ = lean_int_ediv(v_hours_1014_, v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofHours___boxed(
    mut v_hours_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_Time_Week_Offset_ofHours(v_hours_1017_);
    crate::leanh::lean_dec(v_hours_1017_);
    return v_res_1018_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toDays___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_1020_ = lean_nat_to_int(v___x_1019_);
    return v___x_1020_;
}
pub unsafe fn l_Std_Time_Week_Offset_toDays(
    mut v_weeks_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1022_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Week_Offset_toDays___closed__0,
    );
    v___x_1023_ = lean_int_mul(v_weeks_1021_, v___x_1022_);
    return v___x_1023_;
}
pub unsafe fn l_Std_Time_Week_Offset_toDays___boxed(
    mut v_weeks_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Std_Time_Week_Offset_toDays(v_weeks_1024_);
    crate::leanh::lean_dec(v_weeks_1024_);
    return v_res_1025_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofDays(
    mut v_days_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Week_Offset_toDays___closed__0,
    );
    v___x_1028_ = lean_int_ediv(v_days_1026_, v___x_1027_);
    return v___x_1028_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofDays___boxed(
    mut v_days_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Std_Time_Week_Offset_ofDays(v_days_1029_);
    crate::leanh::lean_dec(v_days_1029_);
    return v_res_1030_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Week(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_Week_instLEOrdinal = _init_l_Std_Time_Week_instLEOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instLEOrdinal);
    l_Std_Time_Week_instLTOrdinal = _init_l_Std_Time_Week_instLTOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instLTOrdinal);
    l_Std_Time_Week_instInhabitedOrdinal = _init_l_Std_Time_Week_instInhabitedOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instInhabitedOrdinal);
    l_Std_Time_Week_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset___aux__1);
    l_Std_Time_Week_instInhabitedOffset = _init_l_Std_Time_Week_instInhabitedOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset);
    l_Std_Time_Week_instLEOffset = _init_l_Std_Time_Week_instLEOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instLEOffset);
    l_Std_Time_Week_instLTOffset = _init_l_Std_Time_Week_instLTOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_instLTOffset);
    l_Std_Time_Week_Ordinal_instInhabitedOfMonth =
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_Ordinal_instInhabitedOfMonth);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Week(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Time_Week_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Week_Ordinal_ofNat___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Week_Ordinal_ofNat___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Unit_Week(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Day(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Week(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Week(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Week(builtin);
}
