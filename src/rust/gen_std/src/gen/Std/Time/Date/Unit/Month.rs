// Lean compiler output
// Module: Std.Time.Date.Unit.Month
// Imports: Std.Time.Date.Unit.Day Init.Data.Fin.Lemmas
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_push, lean_int_add,
    lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_div, lean_int_ediv, lean_int_emod,
    lean_int_mul, lean_int_neg, lean_int_sub, lean_mk_empty_array_with_capacity, lean_nat_abs,
    lean_nat_dec_le, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_mul___boxed, l_Int_neg___boxed, l_Int_sub___boxed, l_Int_toNat,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_ediv___boxed;
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_instNatCast___lam__0, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Std::Time::Date::Unit::Day::{
    initialize_Std_Time_Date_Unit_Day, l_Std_Time_Day_instInhabitedOffset,
    runtime_initialize_Std_Time_Date_Unit_Day,
};
static mut l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instReprOrdinal___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instReprOrdinal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instReprOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instReprOrdinal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instLEOrdinal: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instLTOrdinal: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instInhabitedOrdinal: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instOrdOrdinal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instOrdOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instOrdOrdinal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instReprOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instInhabitedOffset___aux__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instInhabitedOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instAddOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Month_instAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_instSubOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Month_instSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_instMulOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instMulOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instMulOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instMulOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instMulOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_instDivOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_ediv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instDivOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instDivOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instDivOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instDivOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_instNegOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Month_instNegOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instNegOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_instToStringOffset___closed__0_value: leanh::LeanClosureObject<
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
static mut l_Std_Time_Month_instToStringOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instToStringOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instToStringOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instToStringOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instLTOffset: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Month_instLEOffset: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Month_instOrdOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instOrdOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instOrdOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instReprQuarter: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instLTQuarter: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instLEQuarter: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instInhabitedQuarter: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instOrdQuarter___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdQuarter___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instOrdQuarter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdQuarter___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Month_instOrdQuarter: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdQuarter___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Month_Quarter_ofMonth___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Quarter_ofMonth___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Quarter_ofMonth___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Quarter_ofMonth___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_january: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_february: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_march: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_april: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_may: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_june: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_july: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_august: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_september: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_october: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_november: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_december: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value:
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
    m_data: [100, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value)
            as *mut leanh::LeanObject,
        14249328086033210933 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_ofNat___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofFin___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofFin___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toMinutes___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toMinutes___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toDays___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toDays___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toDays___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toDays___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = leanh::lean_unsigned_to_nat(0);
    v___x_1021_ = lean_nat_to_int(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___aux__1(
    mut v_n_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    v___x_1024_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1025_ = lean_int_dec_lt(v_n_1022_, v___x_1024_);
    if v___x_1025_ == 0 {
        let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1026_ = l_Int_repr(v_n_1022_);
        v___x_1027_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
        return v___x_1027_;
    } else {
        let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1028_ = l_Int_repr(v_n_1022_);
        v___x_1029_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1029_, 0, v___x_1028_);
        v___x_1030_ = l_Repr_addAppParen(v___x_1029_, v_a_1023_);
        return v___x_1030_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___aux__1___boxed(
    mut v_n_1031_: *mut leanh::LeanObject,
    mut v_a_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Std_Time_Month_instReprOrdinal___aux__1(v_n_1031_, v_a_1032_);
    leanh::lean_dec(v_a_1032_);
    leanh::lean_dec(v_n_1031_);
    return v_res_1033_;
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___lam__0(
    mut v___y_1034_: *mut leanh::LeanObject,
    mut v___y_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    v___x_1036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1037_ = lean_int_dec_lt(v___y_1034_, v___x_1036_);
    if v___x_1037_ == 0 {
        let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1038_ = l_Int_repr(v___y_1034_);
        v___x_1039_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1039_, 0, v___x_1038_);
        return v___x_1039_;
    } else {
        let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1040_ = l_Int_repr(v___y_1034_);
        v___x_1041_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1041_, 0, v___x_1040_);
        v___x_1042_ = l_Repr_addAppParen(v___x_1041_, v___y_1035_);
        return v___x_1042_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___lam__0___boxed(
    mut v___y_1043_: *mut leanh::LeanObject,
    mut v___y_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Std_Time_Month_instReprOrdinal___lam__0(v___y_1043_, v___y_1044_);
    leanh::lean_dec(v___y_1044_);
    leanh::lean_dec(v___y_1043_);
    return v_res_1045_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal___aux__1(
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_b_1049_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1050_: u8 = 0;
    v___x_1050_ = lean_int_dec_eq(v_a_1048_, v_b_1049_);
    return v___x_1050_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_b_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1053_: u8 = 0;
    let mut v_r_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Std_Time_Month_instDecidableEqOrdinal___aux__1(v_a_1051_, v_b_1052_);
    leanh::lean_dec(v_b_1052_);
    leanh::lean_dec(v_a_1051_);
    v_r_1054_ = leanh::lean_box((v_res_1053_) as usize);
    return v_r_1054_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal(
    mut v_a_1055_: *mut leanh::LeanObject,
    mut v_b_1056_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1057_: u8 = 0;
    v___x_1057_ = lean_int_dec_eq(v_a_1055_, v_b_1056_);
    return v___x_1057_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal___boxed(
    mut v_a_1058_: *mut leanh::LeanObject,
    mut v_b_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1060_: u8 = 0;
    let mut v_r_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Std_Time_Month_instDecidableEqOrdinal(v_a_1058_, v_b_1059_);
    leanh::lean_dec(v_b_1059_);
    leanh::lean_dec(v_a_1058_);
    v_r_1061_ = leanh::lean_box((v_res_1060_) as usize);
    return v_r_1061_;
}
pub unsafe fn _init_l_Std_Time_Month_instLEOrdinal() -> *mut leanh::LeanObject {
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = leanh::lean_box(0);
    return v___x_1062_;
}
pub unsafe fn _init_l_Std_Time_Month_instLTOrdinal() -> *mut leanh::LeanObject {
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = leanh::lean_box(0);
    return v___x_1063_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_unsigned_to_nat(1);
    v___x_1065_ = lean_nat_to_int(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = leanh::lean_unsigned_to_nat(11);
    v___x_1067_ = lean_nat_to_int(v___x_1066_);
    return v___x_1067_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_1069_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1070_ = lean_int_add(v___x_1069_, v___x_1068_);
    return v___x_1070_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2,
    );
    v___x_1073_ = lean_int_sub(v___x_1072_, v___x_1071_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1075_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3,
    );
    v_range_1076_ = lean_int_add(v___x_1075_, v___x_1074_);
    return v_range_1076_;
}
pub unsafe fn l_Std_Time_Month_instOfNatOrdinal___aux__1(
    mut v_n_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1079_ = lean_nat_to_int(v_n_1077_);
    v_range_1080_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1081_ = lean_int_sub(v___x_1079_, v___x_1078_);
    leanh::lean_dec(v___x_1079_);
    v___x_1082_ = lean_int_emod(v___x_1081_, v_range_1080_);
    leanh::lean_dec(v___x_1081_);
    v___x_1083_ = lean_int_add(v___x_1082_, v_range_1080_);
    leanh::lean_dec(v___x_1082_);
    v___x_1084_ = lean_int_emod(v___x_1083_, v_range_1080_);
    leanh::lean_dec(v___x_1083_);
    v___x_1085_ = lean_int_add(v___x_1084_, v___x_1078_);
    leanh::lean_dec(v___x_1084_);
    return v___x_1085_;
}
pub unsafe fn l_Std_Time_Month_instOfNatOrdinal(
    mut v_n_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1088_ = lean_nat_to_int(v_n_1086_);
    v_range_1089_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1090_ = lean_int_sub(v___x_1088_, v___x_1087_);
    leanh::lean_dec(v___x_1088_);
    v___x_1091_ = lean_int_emod(v___x_1090_, v_range_1089_);
    leanh::lean_dec(v___x_1090_);
    v___x_1092_ = lean_int_add(v___x_1091_, v_range_1089_);
    leanh::lean_dec(v___x_1091_);
    v___x_1093_ = lean_int_emod(v___x_1092_, v_range_1089_);
    leanh::lean_dec(v___x_1092_);
    v___x_1094_ = lean_int_add(v___x_1093_, v___x_1087_);
    leanh::lean_dec(v___x_1093_);
    return v___x_1094_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1096_ = lean_int_sub(v___x_1095_, v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1()
-> *mut leanh::LeanObject {
    let mut v_range_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1097_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0,
    );
    v___x_1099_ = lean_int_emod(v___x_1098_, v_range_1097_);
    return v___x_1099_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2()
-> *mut leanh::LeanObject {
    let mut v_range_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1100_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1101_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1,
    );
    v___x_1102_ = lean_int_add(v___x_1101_, v_range_1100_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3()
-> *mut leanh::LeanObject {
    let mut v_range_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1103_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1104_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2,
    );
    v___x_1105_ = lean_int_emod(v___x_1104_, v_range_1103_);
    return v___x_1105_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1107_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3,
    );
    v___x_1108_ = lean_int_add(v___x_1107_, v___x_1106_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal() -> *mut leanh::LeanObject {
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4,
    );
    return v___x_1109_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal___aux__1(
    mut v_x_1110_: *mut leanh::LeanObject,
    mut v_y_1111_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1112_: u8 = 0;
    v___x_1112_ = lean_int_dec_le(v_x_1110_, v_y_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_1113_: *mut leanh::LeanObject,
    mut v_y_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1115_: u8 = 0;
    let mut v_r_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Std_Time_Month_instDecidableLeOrdinal___aux__1(v_x_1113_, v_y_1114_);
    leanh::lean_dec(v_y_1114_);
    leanh::lean_dec(v_x_1113_);
    v_r_1116_ = leanh::lean_box((v_res_1115_) as usize);
    return v_r_1116_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal(
    mut v___y_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1119_: u8 = 0;
    v___x_1119_ = lean_int_dec_le(v___y_1117_, v___y_1118_);
    return v___x_1119_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal___boxed(
    mut v___y_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1122_: u8 = 0;
    let mut v_r_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Std_Time_Month_instDecidableLeOrdinal(v___y_1120_, v___y_1121_);
    leanh::lean_dec(v___y_1121_);
    leanh::lean_dec(v___y_1120_);
    v_r_1123_ = leanh::lean_box((v_res_1122_) as usize);
    return v_r_1123_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal___aux__1(
    mut v_x_1124_: *mut leanh::LeanObject,
    mut v_y_1125_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1126_: u8 = 0;
    v___x_1126_ = lean_int_dec_lt(v_x_1124_, v_y_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_1127_: *mut leanh::LeanObject,
    mut v_y_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1129_: u8 = 0;
    let mut v_r_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Std_Time_Month_instDecidableLtOrdinal___aux__1(v_x_1127_, v_y_1128_);
    leanh::lean_dec(v_y_1128_);
    leanh::lean_dec(v_x_1127_);
    v_r_1130_ = leanh::lean_box((v_res_1129_) as usize);
    return v_r_1130_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal(
    mut v___y_1131_: *mut leanh::LeanObject,
    mut v___y_1132_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1133_: u8 = 0;
    v___x_1133_ = lean_int_dec_lt(v___y_1131_, v___y_1132_);
    return v___x_1133_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal___boxed(
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1136_: u8 = 0;
    let mut v_r_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l_Std_Time_Month_instDecidableLtOrdinal(v___y_1134_, v___y_1135_);
    leanh::lean_dec(v___y_1135_);
    leanh::lean_dec(v___y_1134_);
    v_r_1137_ = leanh::lean_box((v_res_1136_) as usize);
    return v_r_1137_;
}
pub unsafe fn l_Std_Time_Month_instOrdOrdinal___aux__1(
    mut v_x_1138_: *mut leanh::LeanObject,
    mut v_y_1139_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1140_: u8 = 0;
    v___x_1140_ = lean_int_dec_lt(v_x_1138_, v_y_1139_);
    if v___x_1140_ == 0 {
        let mut v___x_1141_: u8 = 0;
        v___x_1141_ = lean_int_dec_eq(v_x_1138_, v_y_1139_);
        if v___x_1141_ == 0 {
            let mut v___x_1142_: u8 = 0;
            v___x_1142_ = 2;
            return v___x_1142_;
        } else {
            let mut v___x_1143_: u8 = 0;
            v___x_1143_ = 1;
            return v___x_1143_;
        }
    } else {
        let mut v___x_1144_: u8 = 0;
        v___x_1144_ = 0;
        return v___x_1144_;
    }
}
pub unsafe fn l_Std_Time_Month_instOrdOrdinal___aux__1___boxed(
    mut v_x_1145_: *mut leanh::LeanObject,
    mut v_y_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1147_: u8 = 0;
    let mut v_r_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1147_ = l_Std_Time_Month_instOrdOrdinal___aux__1(v_x_1145_, v_y_1146_);
    leanh::lean_dec(v_y_1146_);
    leanh::lean_dec(v_x_1145_);
    v_r_1148_ = leanh::lean_box((v_res_1147_) as usize);
    return v_r_1148_;
}
pub unsafe fn l_Std_Time_Month_instReprOffset___aux__1(
    mut v_i_1151_: *mut leanh::LeanObject,
    mut v_prec_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    v___x_1153_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1154_ = lean_int_dec_lt(v_i_1151_, v___x_1153_);
    if v___x_1154_ == 0 {
        let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1155_ = l_Int_repr(v_i_1151_);
        v___x_1156_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
        return v___x_1156_;
    } else {
        let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1157_ = l_Int_repr(v_i_1151_);
        v___x_1158_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
        v___x_1159_ = l_Repr_addAppParen(v___x_1158_, v_prec_1152_);
        return v___x_1159_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprOffset___aux__1___boxed(
    mut v_i_1160_: *mut leanh::LeanObject,
    mut v_prec_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_Time_Month_instReprOffset___aux__1(v_i_1160_, v_prec_1161_);
    leanh::lean_dec(v_prec_1161_);
    leanh::lean_dec(v_i_1160_);
    return v_res_1162_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset___aux__1(
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_b_1165_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1166_: u8 = 0;
    v___x_1166_ = lean_int_dec_eq(v_a_1164_, v_b_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset___aux__1___boxed(
    mut v_a_1167_: *mut leanh::LeanObject,
    mut v_b_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1169_: u8 = 0;
    let mut v_r_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Std_Time_Month_instDecidableEqOffset___aux__1(v_a_1167_, v_b_1168_);
    leanh::lean_dec(v_b_1168_);
    leanh::lean_dec(v_a_1167_);
    v_r_1170_ = leanh::lean_box((v_res_1169_) as usize);
    return v_r_1170_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset(
    mut v_a_1171_: *mut leanh::LeanObject,
    mut v_b_1172_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1173_: u8 = 0;
    v___x_1173_ = lean_int_dec_eq(v_a_1171_, v_b_1172_);
    return v___x_1173_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset___boxed(
    mut v_a_1174_: *mut leanh::LeanObject,
    mut v_b_1175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1176_: u8 = 0;
    let mut v_r_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Std_Time_Month_instDecidableEqOffset(v_a_1174_, v_b_1175_);
    leanh::lean_dec(v_b_1175_);
    leanh::lean_dec(v_a_1174_);
    v_r_1177_ = leanh::lean_box((v_res_1176_) as usize);
    return v_r_1177_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOffset___aux__1() -> *mut leanh::LeanObject
{
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    return v___x_1178_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOffset() -> *mut leanh::LeanObject {
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    return v___x_1179_;
}
pub unsafe fn l_Std_Time_Month_instAddOffset___aux__1(
    mut v_m_1180_: *mut leanh::LeanObject,
    mut v_n_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_int_add(v_m_1180_, v_n_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Std_Time_Month_instAddOffset___aux__1___boxed(
    mut v_m_1183_: *mut leanh::LeanObject,
    mut v_n_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1185_ = l_Std_Time_Month_instAddOffset___aux__1(v_m_1183_, v_n_1184_);
    leanh::lean_dec(v_n_1184_);
    leanh::lean_dec(v_m_1183_);
    return v_res_1185_;
}
pub unsafe fn l_Std_Time_Month_instSubOffset___aux__1(
    mut v_m_1188_: *mut leanh::LeanObject,
    mut v_n_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = lean_int_sub(v_m_1188_, v_n_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Std_Time_Month_instSubOffset___aux__1___boxed(
    mut v_m_1191_: *mut leanh::LeanObject,
    mut v_n_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Std_Time_Month_instSubOffset___aux__1(v_m_1191_, v_n_1192_);
    leanh::lean_dec(v_n_1192_);
    leanh::lean_dec(v_m_1191_);
    return v_res_1193_;
}
pub unsafe fn l_Std_Time_Month_instMulOffset___aux__1(
    mut v_m_1196_: *mut leanh::LeanObject,
    mut v_n_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = lean_int_mul(v_m_1196_, v_n_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Std_Time_Month_instMulOffset___aux__1___boxed(
    mut v_m_1199_: *mut leanh::LeanObject,
    mut v_n_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Std_Time_Month_instMulOffset___aux__1(v_m_1199_, v_n_1200_);
    leanh::lean_dec(v_n_1200_);
    leanh::lean_dec(v_m_1199_);
    return v_res_1201_;
}
pub unsafe fn l_Std_Time_Month_instDivOffset___aux__1(
    mut v_a_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = lean_int_ediv(v_a_1204_, v_a_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Std_Time_Month_instDivOffset___aux__1___boxed(
    mut v_a_1207_: *mut leanh::LeanObject,
    mut v_a_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Std_Time_Month_instDivOffset___aux__1(v_a_1207_, v_a_1208_);
    leanh::lean_dec(v_a_1208_);
    leanh::lean_dec(v_a_1207_);
    return v_res_1209_;
}
pub unsafe fn l_Std_Time_Month_instNegOffset___aux__1(
    mut v_n_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = lean_int_neg(v_n_1212_);
    return v___x_1213_;
}
pub unsafe fn l_Std_Time_Month_instNegOffset___aux__1___boxed(
    mut v_n_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Std_Time_Month_instNegOffset___aux__1(v_n_1214_);
    leanh::lean_dec(v_n_1214_);
    return v_res_1215_;
}
pub unsafe fn l_Std_Time_Month_instToStringOffset___aux__1(
    mut v_a_1218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Int_repr(v_a_1218_);
    return v___x_1219_;
}
pub unsafe fn l_Std_Time_Month_instToStringOffset___aux__1___boxed(
    mut v_a_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Std_Time_Month_instToStringOffset___aux__1(v_a_1220_);
    leanh::lean_dec(v_a_1220_);
    return v_res_1221_;
}
pub unsafe fn _init_l_Std_Time_Month_instLTOffset() -> *mut leanh::LeanObject {
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1224_ = leanh::lean_box(0);
    return v___x_1224_;
}
pub unsafe fn _init_l_Std_Time_Month_instLEOffset() -> *mut leanh::LeanObject {
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ = leanh::lean_box(0);
    return v___x_1225_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOffset(
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1228_: u8 = 0;
    v___x_1228_ = lean_int_dec_le(v___y_1226_, v___y_1227_);
    return v___x_1228_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOffset___boxed(
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1231_: u8 = 0;
    let mut v_r_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_Std_Time_Month_instDecidableLeOffset(v___y_1229_, v___y_1230_);
    leanh::lean_dec(v___y_1230_);
    leanh::lean_dec(v___y_1229_);
    v_r_1232_ = leanh::lean_box((v_res_1231_) as usize);
    return v_r_1232_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOffset(
    mut v___y_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1235_: u8 = 0;
    v___x_1235_ = lean_int_dec_lt(v___y_1233_, v___y_1234_);
    return v___x_1235_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOffset___boxed(
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1238_: u8 = 0;
    let mut v_r_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ = l_Std_Time_Month_instDecidableLtOffset(v___y_1236_, v___y_1237_);
    leanh::lean_dec(v___y_1237_);
    leanh::lean_dec(v___y_1236_);
    v_r_1239_ = leanh::lean_box((v_res_1238_) as usize);
    return v_r_1239_;
}
pub unsafe fn l_Std_Time_Month_instOfNatOffset(
    mut v_n_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1241_ = lean_nat_to_int(v_n_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Std_Time_Month_instOrdOffset___aux__1(
    mut v_x_1242_: *mut leanh::LeanObject,
    mut v_y_1243_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1244_: u8 = 0;
    v___x_1244_ = lean_int_dec_lt(v_x_1242_, v_y_1243_);
    if v___x_1244_ == 0 {
        let mut v___x_1245_: u8 = 0;
        v___x_1245_ = lean_int_dec_eq(v_x_1242_, v_y_1243_);
        if v___x_1245_ == 0 {
            let mut v___x_1246_: u8 = 0;
            v___x_1246_ = 2;
            return v___x_1246_;
        } else {
            let mut v___x_1247_: u8 = 0;
            v___x_1247_ = 1;
            return v___x_1247_;
        }
    } else {
        let mut v___x_1248_: u8 = 0;
        v___x_1248_ = 0;
        return v___x_1248_;
    }
}
pub unsafe fn l_Std_Time_Month_instOrdOffset___aux__1___boxed(
    mut v_x_1249_: *mut leanh::LeanObject,
    mut v_y_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1251_: u8 = 0;
    let mut v_r_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Std_Time_Month_instOrdOffset___aux__1(v_x_1249_, v_y_1250_);
    leanh::lean_dec(v_y_1250_);
    leanh::lean_dec(v_x_1249_);
    v_r_1252_ = leanh::lean_box((v_res_1251_) as usize);
    return v_r_1252_;
}
pub unsafe fn l_Std_Time_Month_instReprQuarter___aux__1(
    mut v_n_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u8 = 0;
    v___x_1257_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1258_ = lean_int_dec_lt(v_n_1255_, v___x_1257_);
    if v___x_1258_ == 0 {
        let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1259_ = l_Int_repr(v_n_1255_);
        v___x_1260_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1260_, 0, v___x_1259_);
        return v___x_1260_;
    } else {
        let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1261_ = l_Int_repr(v_n_1255_);
        v___x_1262_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1262_, 0, v___x_1261_);
        v___x_1263_ = l_Repr_addAppParen(v___x_1262_, v_a_1256_);
        return v___x_1263_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprQuarter___aux__1___boxed(
    mut v_n_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Std_Time_Month_instReprQuarter___aux__1(v_n_1264_, v_a_1265_);
    leanh::lean_dec(v_a_1265_);
    leanh::lean_dec(v_n_1264_);
    return v_res_1266_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter___aux__1(
    mut v_a_1268_: *mut leanh::LeanObject,
    mut v_b_1269_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1270_: u8 = 0;
    v___x_1270_ = lean_int_dec_eq(v_a_1268_, v_b_1269_);
    return v___x_1270_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter___aux__1___boxed(
    mut v_a_1271_: *mut leanh::LeanObject,
    mut v_b_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1273_: u8 = 0;
    let mut v_r_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Std_Time_Month_instDecidableEqQuarter___aux__1(v_a_1271_, v_b_1272_);
    leanh::lean_dec(v_b_1272_);
    leanh::lean_dec(v_a_1271_);
    v_r_1274_ = leanh::lean_box((v_res_1273_) as usize);
    return v_r_1274_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter(
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_b_1276_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1277_: u8 = 0;
    v___x_1277_ = lean_int_dec_eq(v_a_1275_, v_b_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter___boxed(
    mut v_a_1278_: *mut leanh::LeanObject,
    mut v_b_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1280_: u8 = 0;
    let mut v_r_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Std_Time_Month_instDecidableEqQuarter(v_a_1278_, v_b_1279_);
    leanh::lean_dec(v_b_1279_);
    leanh::lean_dec(v_a_1278_);
    v_r_1281_ = leanh::lean_box((v_res_1280_) as usize);
    return v_r_1281_;
}
pub unsafe fn _init_l_Std_Time_Month_instLTQuarter() -> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = leanh::lean_box(0);
    return v___x_1282_;
}
pub unsafe fn _init_l_Std_Time_Month_instLEQuarter() -> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = leanh::lean_box(0);
    return v___x_1283_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = leanh::lean_unsigned_to_nat(3);
    v___x_1285_ = lean_nat_to_int(v___x_1284_);
    return v___x_1285_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0,
    );
    v___x_1287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1288_ = lean_int_add(v___x_1287_, v___x_1286_);
    return v___x_1288_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1,
    );
    v___x_1291_ = lean_int_sub(v___x_1290_, v___x_1289_);
    return v___x_1291_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1292_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2,
    );
    v_range_1294_ = lean_int_add(v___x_1293_, v___x_1292_);
    return v_range_1294_;
}
pub unsafe fn l_Std_Time_Month_instOfNatQuarter___aux__1(
    mut v_n_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1296_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1297_ = lean_nat_to_int(v_n_1295_);
    v_range_1298_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1299_ = lean_int_sub(v___x_1297_, v___x_1296_);
    leanh::lean_dec(v___x_1297_);
    v___x_1300_ = lean_int_emod(v___x_1299_, v_range_1298_);
    leanh::lean_dec(v___x_1299_);
    v___x_1301_ = lean_int_add(v___x_1300_, v_range_1298_);
    leanh::lean_dec(v___x_1300_);
    v___x_1302_ = lean_int_emod(v___x_1301_, v_range_1298_);
    leanh::lean_dec(v___x_1301_);
    v___x_1303_ = lean_int_add(v___x_1302_, v___x_1296_);
    leanh::lean_dec(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Std_Time_Month_instOfNatQuarter(
    mut v_n_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1306_ = lean_nat_to_int(v_n_1304_);
    v_range_1307_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1308_ = lean_int_sub(v___x_1306_, v___x_1305_);
    leanh::lean_dec(v___x_1306_);
    v___x_1309_ = lean_int_emod(v___x_1308_, v_range_1307_);
    leanh::lean_dec(v___x_1308_);
    v___x_1310_ = lean_int_add(v___x_1309_, v_range_1307_);
    leanh::lean_dec(v___x_1309_);
    v___x_1311_ = lean_int_emod(v___x_1310_, v_range_1307_);
    leanh::lean_dec(v___x_1310_);
    v___x_1312_ = lean_int_add(v___x_1311_, v___x_1305_);
    leanh::lean_dec(v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__0()
-> *mut leanh::LeanObject {
    let mut v_range_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1314_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0,
    );
    v___x_1315_ = lean_int_emod(v___x_1314_, v_range_1313_);
    return v___x_1315_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__1()
-> *mut leanh::LeanObject {
    let mut v_range_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1316_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1317_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__0_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__0,
    );
    v___x_1318_ = lean_int_add(v___x_1317_, v_range_1316_);
    return v___x_1318_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__2()
-> *mut leanh::LeanObject {
    let mut v_range_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1319_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1320_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__1_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__1,
    );
    v___x_1321_ = lean_int_emod(v___x_1320_, v_range_1319_);
    return v___x_1321_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1323_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__2_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__2,
    );
    v___x_1324_ = lean_int_add(v___x_1323_, v___x_1322_);
    return v___x_1324_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter() -> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__3_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__3,
    );
    return v___x_1325_;
}
pub unsafe fn l_Std_Time_Month_instOrdQuarter___aux__1(
    mut v_x_1326_: *mut leanh::LeanObject,
    mut v_y_1327_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1328_: u8 = 0;
    v___x_1328_ = lean_int_dec_lt(v_x_1326_, v_y_1327_);
    if v___x_1328_ == 0 {
        let mut v___x_1329_: u8 = 0;
        v___x_1329_ = lean_int_dec_eq(v_x_1326_, v_y_1327_);
        if v___x_1329_ == 0 {
            let mut v___x_1330_: u8 = 0;
            v___x_1330_ = 2;
            return v___x_1330_;
        } else {
            let mut v___x_1331_: u8 = 0;
            v___x_1331_ = 1;
            return v___x_1331_;
        }
    } else {
        let mut v___x_1332_: u8 = 0;
        v___x_1332_ = 0;
        return v___x_1332_;
    }
}
pub unsafe fn l_Std_Time_Month_instOrdQuarter___aux__1___boxed(
    mut v_x_1333_: *mut leanh::LeanObject,
    mut v_y_1334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1335_: u8 = 0;
    let mut v_r_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1335_ = l_Std_Time_Month_instOrdQuarter___aux__1(v_x_1333_, v_y_1334_);
    leanh::lean_dec(v_y_1334_);
    leanh::lean_dec(v_x_1333_);
    v_r_1336_ = leanh::lean_box((v_res_1335_) as usize);
    return v_r_1336_;
}
pub unsafe fn _init_l_Std_Time_Month_Quarter_ofMonth___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = leanh::lean_unsigned_to_nat(3);
    v___x_1340_ = lean_nat_to_int(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l_Std_Time_Month_Quarter_ofMonth___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1342_ = lean_int_neg(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l_Std_Time_Month_Quarter_ofMonth(
    mut v_month_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1345_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__0_once),
        _init_l_Std_Time_Month_Quarter_ofMonth___closed__0,
    );
    v___x_1346_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1_once),
        _init_l_Std_Time_Month_Quarter_ofMonth___closed__1,
    );
    v___x_1347_ = lean_int_add(v_month_1343_, v___x_1346_);
    v___x_1348_ = lean_int_ediv(v___x_1347_, v___x_1345_);
    leanh::lean_dec(v___x_1347_);
    v___x_1349_ = lean_int_add(v___x_1348_, v___x_1344_);
    leanh::lean_dec(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_Std_Time_Month_Quarter_ofMonth___boxed(
    mut v_month_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1351_ = l_Std_Time_Month_Quarter_ofMonth(v_month_1350_);
    leanh::lean_dec(v_month_1350_);
    return v_res_1351_;
}
pub unsafe fn l_Std_Time_Month_Offset_ofNat(
    mut v_data_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = lean_nat_to_int(v_data_1352_);
    return v___x_1353_;
}
pub unsafe fn l_Std_Time_Month_Offset_ofInt(
    mut v_data_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_1354_);
    return v_data_1354_;
}
pub unsafe fn l_Std_Time_Month_Offset_ofInt___boxed(
    mut v_data_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_Std_Time_Month_Offset_ofInt(v_data_1355_);
    leanh::lean_dec(v_data_1355_);
    return v_res_1356_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_january() -> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4,
    );
    return v___x_1357_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = leanh::lean_unsigned_to_nat(2);
    v___x_1359_ = lean_nat_to_int(v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1361_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__0,
    );
    v___x_1362_ = lean_int_sub(v___x_1361_, v___x_1360_);
    return v___x_1362_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__2() -> *mut leanh::LeanObject
{
    let mut v_range_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__1,
    );
    v___x_1365_ = lean_int_emod(v___x_1364_, v_range_1363_);
    return v___x_1365_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__3() -> *mut leanh::LeanObject
{
    let mut v_range_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1367_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__2,
    );
    v___x_1368_ = lean_int_add(v___x_1367_, v_range_1366_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__4() -> *mut leanh::LeanObject
{
    let mut v_range_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__3,
    );
    v___x_1371_ = lean_int_emod(v___x_1370_, v_range_1369_);
    return v___x_1371_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__4,
    );
    v___x_1374_ = lean_int_add(v___x_1373_, v___x_1372_);
    return v___x_1374_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february() -> *mut leanh::LeanObject {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__5,
    );
    return v___x_1375_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0,
    );
    v___x_1378_ = lean_int_sub(v___x_1377_, v___x_1376_);
    return v___x_1378_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__1() -> *mut leanh::LeanObject {
    let mut v_range_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__0,
    );
    v___x_1381_ = lean_int_emod(v___x_1380_, v_range_1379_);
    return v___x_1381_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__2() -> *mut leanh::LeanObject {
    let mut v_range_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1382_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__1,
    );
    v___x_1384_ = lean_int_add(v___x_1383_, v_range_1382_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__3() -> *mut leanh::LeanObject {
    let mut v_range_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1385_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1386_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__2,
    );
    v___x_1387_ = lean_int_emod(v___x_1386_, v_range_1385_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1389_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__3,
    );
    v___x_1390_ = lean_int_add(v___x_1389_, v___x_1388_);
    return v___x_1390_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march() -> *mut leanh::LeanObject {
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__4,
    );
    return v___x_1391_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = leanh::lean_unsigned_to_nat(4);
    v___x_1393_ = lean_nat_to_int(v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__0,
    );
    v___x_1396_ = lean_int_sub(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__2() -> *mut leanh::LeanObject {
    let mut v_range_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__1,
    );
    v___x_1399_ = lean_int_emod(v___x_1398_, v_range_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__3() -> *mut leanh::LeanObject {
    let mut v_range_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__2,
    );
    v___x_1402_ = lean_int_add(v___x_1401_, v_range_1400_);
    return v___x_1402_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__4() -> *mut leanh::LeanObject {
    let mut v_range_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1403_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__3,
    );
    v___x_1405_ = lean_int_emod(v___x_1404_, v_range_1403_);
    return v___x_1405_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1407_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__4,
    );
    v___x_1408_ = lean_int_add(v___x_1407_, v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april() -> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__5,
    );
    return v___x_1409_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = leanh::lean_unsigned_to_nat(5);
    v___x_1411_ = lean_nat_to_int(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__0,
    );
    v___x_1414_ = lean_int_sub(v___x_1413_, v___x_1412_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__2() -> *mut leanh::LeanObject {
    let mut v_range_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1415_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__1,
    );
    v___x_1417_ = lean_int_emod(v___x_1416_, v_range_1415_);
    return v___x_1417_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__3() -> *mut leanh::LeanObject {
    let mut v_range_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1419_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__2,
    );
    v___x_1420_ = lean_int_add(v___x_1419_, v_range_1418_);
    return v___x_1420_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__4() -> *mut leanh::LeanObject {
    let mut v_range_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1421_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__3,
    );
    v___x_1423_ = lean_int_emod(v___x_1422_, v_range_1421_);
    return v___x_1423_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__4,
    );
    v___x_1426_ = lean_int_add(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may() -> *mut leanh::LeanObject {
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__5,
    );
    return v___x_1427_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = leanh::lean_unsigned_to_nat(6);
    v___x_1429_ = lean_nat_to_int(v___x_1428_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1431_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__0,
    );
    v___x_1432_ = lean_int_sub(v___x_1431_, v___x_1430_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__2() -> *mut leanh::LeanObject {
    let mut v_range_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1434_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__1,
    );
    v___x_1435_ = lean_int_emod(v___x_1434_, v_range_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__3() -> *mut leanh::LeanObject {
    let mut v_range_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1436_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1437_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__2,
    );
    v___x_1438_ = lean_int_add(v___x_1437_, v_range_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__4() -> *mut leanh::LeanObject {
    let mut v_range_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1440_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__3,
    );
    v___x_1441_ = lean_int_emod(v___x_1440_, v_range_1439_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1443_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__4,
    );
    v___x_1444_ = lean_int_add(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june() -> *mut leanh::LeanObject {
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__5,
    );
    return v___x_1445_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = leanh::lean_unsigned_to_nat(7);
    v___x_1447_ = lean_nat_to_int(v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1449_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__0,
    );
    v___x_1450_ = lean_int_sub(v___x_1449_, v___x_1448_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__2() -> *mut leanh::LeanObject {
    let mut v_range_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1451_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__1,
    );
    v___x_1453_ = lean_int_emod(v___x_1452_, v_range_1451_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__3() -> *mut leanh::LeanObject {
    let mut v_range_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1454_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1455_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__2,
    );
    v___x_1456_ = lean_int_add(v___x_1455_, v_range_1454_);
    return v___x_1456_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__4() -> *mut leanh::LeanObject {
    let mut v_range_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1457_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1458_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__3,
    );
    v___x_1459_ = lean_int_emod(v___x_1458_, v_range_1457_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1461_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__4,
    );
    v___x_1462_ = lean_int_add(v___x_1461_, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july() -> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__5,
    );
    return v___x_1463_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_unsigned_to_nat(8);
    v___x_1465_ = lean_nat_to_int(v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1466_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1467_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__0,
    );
    v___x_1468_ = lean_int_sub(v___x_1467_, v___x_1466_);
    return v___x_1468_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__2() -> *mut leanh::LeanObject {
    let mut v_range_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1469_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1470_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__1,
    );
    v___x_1471_ = lean_int_emod(v___x_1470_, v_range_1469_);
    return v___x_1471_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__3() -> *mut leanh::LeanObject {
    let mut v_range_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1472_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1473_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__2,
    );
    v___x_1474_ = lean_int_add(v___x_1473_, v_range_1472_);
    return v___x_1474_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__4() -> *mut leanh::LeanObject {
    let mut v_range_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1475_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1476_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__3,
    );
    v___x_1477_ = lean_int_emod(v___x_1476_, v_range_1475_);
    return v___x_1477_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__4,
    );
    v___x_1480_ = lean_int_add(v___x_1479_, v___x_1478_);
    return v___x_1480_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august() -> *mut leanh::LeanObject {
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__5,
    );
    return v___x_1481_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1482_ = leanh::lean_unsigned_to_nat(9);
    v___x_1483_ = lean_nat_to_int(v___x_1482_);
    return v___x_1483_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__0,
    );
    v___x_1486_ = lean_int_sub(v___x_1485_, v___x_1484_);
    return v___x_1486_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__2() -> *mut leanh::LeanObject
{
    let mut v_range_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1487_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1488_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__1,
    );
    v___x_1489_ = lean_int_emod(v___x_1488_, v_range_1487_);
    return v___x_1489_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__3() -> *mut leanh::LeanObject
{
    let mut v_range_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1491_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__2,
    );
    v___x_1492_ = lean_int_add(v___x_1491_, v_range_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__4() -> *mut leanh::LeanObject
{
    let mut v_range_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1493_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__3,
    );
    v___x_1495_ = lean_int_emod(v___x_1494_, v_range_1493_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1497_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__4,
    );
    v___x_1498_ = lean_int_add(v___x_1497_, v___x_1496_);
    return v___x_1498_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september() -> *mut leanh::LeanObject {
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__5,
    );
    return v___x_1499_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = leanh::lean_unsigned_to_nat(10);
    v___x_1501_ = lean_nat_to_int(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1503_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__0,
    );
    v___x_1504_ = lean_int_sub(v___x_1503_, v___x_1502_);
    return v___x_1504_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__2() -> *mut leanh::LeanObject
{
    let mut v_range_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1505_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1506_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__1,
    );
    v___x_1507_ = lean_int_emod(v___x_1506_, v_range_1505_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__3() -> *mut leanh::LeanObject
{
    let mut v_range_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1509_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__2,
    );
    v___x_1510_ = lean_int_add(v___x_1509_, v_range_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__4() -> *mut leanh::LeanObject
{
    let mut v_range_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1511_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1512_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__3,
    );
    v___x_1513_ = lean_int_emod(v___x_1512_, v_range_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1515_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__4,
    );
    v___x_1516_ = lean_int_add(v___x_1515_, v___x_1514_);
    return v___x_1516_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october() -> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__5,
    );
    return v___x_1517_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1519_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_1520_ = lean_int_sub(v___x_1519_, v___x_1518_);
    return v___x_1520_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__1() -> *mut leanh::LeanObject
{
    let mut v_range_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1521_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1522_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__0,
    );
    v___x_1523_ = lean_int_emod(v___x_1522_, v_range_1521_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__2() -> *mut leanh::LeanObject
{
    let mut v_range_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1525_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__1,
    );
    v___x_1526_ = lean_int_add(v___x_1525_, v_range_1524_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__3() -> *mut leanh::LeanObject
{
    let mut v_range_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1528_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__2,
    );
    v___x_1529_ = lean_int_emod(v___x_1528_, v_range_1527_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1531_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__3,
    );
    v___x_1532_ = lean_int_add(v___x_1531_, v___x_1530_);
    return v___x_1532_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november() -> *mut leanh::LeanObject {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__4,
    );
    return v___x_1533_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = leanh::lean_unsigned_to_nat(12);
    v___x_1535_ = lean_nat_to_int(v___x_1534_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1537_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__0,
    );
    v___x_1538_ = lean_int_sub(v___x_1537_, v___x_1536_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__2() -> *mut leanh::LeanObject
{
    let mut v_range_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1539_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1540_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__1,
    );
    v___x_1541_ = lean_int_emod(v___x_1540_, v_range_1539_);
    return v___x_1541_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__3() -> *mut leanh::LeanObject
{
    let mut v_range_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1542_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1543_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__2,
    );
    v___x_1544_ = lean_int_add(v___x_1543_, v_range_1542_);
    return v___x_1544_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__4() -> *mut leanh::LeanObject
{
    let mut v_range_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1545_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1546_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__3,
    );
    v___x_1547_ = lean_int_emod(v___x_1546_, v_range_1545_);
    return v___x_1547_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1549_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__4,
    );
    v___x_1550_ = lean_int_add(v___x_1549_, v___x_1548_);
    return v___x_1550_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december() -> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__5,
    );
    return v___x_1551_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toOffset(
    mut v_month_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_month_1552_);
    return v_month_1552_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toOffset___boxed(
    mut v_month_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Std_Time_Month_Ordinal_toOffset(v_month_1553_);
    leanh::lean_dec(v_month_1553_);
    return v_res_1554_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt___redArg(
    mut v_data_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_1555_);
    return v_data_1555_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt___redArg___boxed(
    mut v_data_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l_Std_Time_Month_Ordinal_ofInt___redArg(v_data_1556_);
    leanh::lean_dec(v_data_1556_);
    return v_res_1557_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt(
    mut v_data_1558_: *mut leanh::LeanObject,
    mut v_h_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_1558_);
    return v_data_1558_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt___boxed(
    mut v_data_1560_: *mut leanh::LeanObject,
    mut v_h_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1562_ = l_Std_Time_Month_Ordinal_ofInt(v_data_1560_, v_h_1561_);
    leanh::lean_dec(v_data_1560_);
    return v_res_1562_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10;
    v___x_1590_ = l_Lean_mkAtom(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12,
    );
    v___x_1592_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1593_ = lean_array_push(v___x_1592_, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16;
    v___x_1605_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1606_ = lean_array_push(v___x_1605_, v___x_1604_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17,
    );
    v___x_1608_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15;
    v___x_1609_ = leanh::lean_box(2);
    v___x_1610_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    leanh::lean_ctor_set(v___x_1610_, 1, v___x_1608_);
    leanh::lean_ctor_set(v___x_1610_, 2, v___x_1607_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18,
    );
    v___x_1612_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13,
    );
    v___x_1613_ = lean_array_push(v___x_1612_, v___x_1611_);
    return v___x_1613_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19,
    );
    v___x_1615_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11;
    v___x_1616_ = leanh::lean_box(2);
    v___x_1617_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
    leanh::lean_ctor_set(v___x_1617_, 1, v___x_1615_);
    leanh::lean_ctor_set(v___x_1617_, 2, v___x_1614_);
    return v___x_1617_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20,
    );
    v___x_1619_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1620_ = lean_array_push(v___x_1619_, v___x_1618_);
    return v___x_1620_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21,
    );
    v___x_1622_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9;
    v___x_1623_ = leanh::lean_box(2);
    v___x_1624_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1624_, 0, v___x_1623_);
    leanh::lean_ctor_set(v___x_1624_, 1, v___x_1622_);
    leanh::lean_ctor_set(v___x_1624_, 2, v___x_1621_);
    return v___x_1624_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22,
    );
    v___x_1626_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1627_ = lean_array_push(v___x_1626_, v___x_1625_);
    return v___x_1627_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23,
    );
    v___x_1629_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7;
    v___x_1630_ = leanh::lean_box(2);
    v___x_1631_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1631_, 0, v___x_1630_);
    leanh::lean_ctor_set(v___x_1631_, 1, v___x_1629_);
    leanh::lean_ctor_set(v___x_1631_, 2, v___x_1628_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24,
    );
    v___x_1633_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1634_ = lean_array_push(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25,
    );
    v___x_1636_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4;
    v___x_1637_ = leanh::lean_box(2);
    v___x_1638_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    leanh::lean_ctor_set(v___x_1638_, 1, v___x_1636_);
    leanh::lean_ctor_set(v___x_1638_, 2, v___x_1635_);
    return v___x_1638_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26,
    );
    return v___x_1639_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofNat___redArg(
    mut v_data_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = lean_nat_to_int(v_data_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofNat(
    mut v_data_1642_: *mut leanh::LeanObject,
    mut v_h_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = lean_nat_to_int(v_data_1642_);
    return v___x_1644_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toNat(
    mut v_month_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1647_: u8 = 0;
    let mut v_a_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_intZero_1646_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v_isNeg_1647_ = lean_int_dec_lt(v_month_1645_, v_intZero_1646_);
    v_a_1648_ = lean_nat_abs(v_month_1645_);
    return v_a_1648_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toNat___boxed(
    mut v_month_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1650_ = l_Std_Time_Month_Ordinal_toNat(v_month_1649_);
    leanh::lean_dec(v_month_1649_);
    return v_res_1650_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofFin___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = leanh::lean_unsigned_to_nat(1);
    v___x_1652_ = lean_nat_to_int(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofFin(
    mut v_data_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    v___x_1654_ = leanh::lean_unsigned_to_nat(1);
    v___x_1655_ = lean_nat_dec_le(v___x_1654_, v_data_1653_);
    if v___x_1655_ == 0 {
        let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_data_1653_);
        v___x_1656_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofFin___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofFin___closed__0_once),
            _init_l_Std_Time_Month_Ordinal_ofFin___closed__0,
        );
        return v___x_1656_;
    } else {
        let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1657_ = lean_nat_to_int(v_data_1653_);
        return v___x_1657_;
    }
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__1(
    mut v_a_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_nat_to_int(v_a_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__2(
    mut v_a_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Rat_ofInt(v_a_1660_);
    return v___x_1661_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ = leanh::lean_unsigned_to_nat(31);
    v___x_1663_ = lean_nat_to_int(v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = leanh::lean_unsigned_to_nat(59);
    v___x_1665_ = lean_nat_to_int(v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = leanh::lean_unsigned_to_nat(90);
    v___x_1667_ = lean_nat_to_int(v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = leanh::lean_unsigned_to_nat(120);
    v___x_1669_ = lean_nat_to_int(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = leanh::lean_unsigned_to_nat(151);
    v___x_1671_ = lean_nat_to_int(v___x_1670_);
    return v___x_1671_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1672_ = leanh::lean_unsigned_to_nat(181);
    v___x_1673_ = lean_nat_to_int(v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = leanh::lean_unsigned_to_nat(212);
    v___x_1675_ = lean_nat_to_int(v___x_1674_);
    return v___x_1675_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = leanh::lean_unsigned_to_nat(243);
    v___x_1677_ = lean_nat_to_int(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = leanh::lean_unsigned_to_nat(273);
    v___x_1679_ = lean_nat_to_int(v___x_1678_);
    return v___x_1679_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = leanh::lean_unsigned_to_nat(304);
    v___x_1681_ = lean_nat_to_int(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = leanh::lean_unsigned_to_nat(334);
    v___x_1683_ = lean_nat_to_int(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysAcc_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__10_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10,
    );
    v___x_1685_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__9_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9,
    );
    v___x_1686_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__8_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8,
    );
    v___x_1687_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__7_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7,
    );
    v___x_1688_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__6_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6,
    );
    v___x_1689_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5,
    );
    v___x_1690_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4,
    );
    v___x_1691_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3,
    );
    v___x_1692_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2,
    );
    v___x_1693_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1,
    );
    v___x_1694_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0,
    );
    v_intZero_1695_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1696_ = leanh::lean_unsigned_to_nat(12);
    v___x_1697_ = lean_mk_empty_array_with_capacity(v___x_1696_);
    v___x_1698_ = lean_array_push(v___x_1697_, v_intZero_1695_);
    v___x_1699_ = lean_array_push(v___x_1698_, v___x_1694_);
    v___x_1700_ = lean_array_push(v___x_1699_, v___x_1693_);
    v___x_1701_ = lean_array_push(v___x_1700_, v___x_1692_);
    v___x_1702_ = lean_array_push(v___x_1701_, v___x_1691_);
    v___x_1703_ = lean_array_push(v___x_1702_, v___x_1690_);
    v___x_1704_ = lean_array_push(v___x_1703_, v___x_1689_);
    v___x_1705_ = lean_array_push(v___x_1704_, v___x_1688_);
    v___x_1706_ = lean_array_push(v___x_1705_, v___x_1687_);
    v___x_1707_ = lean_array_push(v___x_1706_, v___x_1686_);
    v___x_1708_ = lean_array_push(v___x_1707_, v___x_1685_);
    v_daysAcc_1709_ = lean_array_push(v___x_1708_, v___x_1684_);
    return v_daysAcc_1709_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = leanh::lean_unsigned_to_nat(86400);
    v___x_1711_ = lean_nat_to_int(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toSeconds(
    mut v_leap_1712_: u8,
    mut v_month_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1715_: u8 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysAcc_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_days_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_intZero_1714_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v_isNeg_1715_ = lean_int_dec_lt(v_month_1713_, v_intZero_1714_);
    v___x_1716_ = l_Std_Time_Day_instInhabitedOffset;
    v_a_1717_ = lean_nat_abs(v_month_1713_);
    v_daysAcc_1718_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11,
    );
    v_days_1719_ = lean_array_get_borrowed(v___x_1716_, v_daysAcc_1718_, v_a_1717_);
    v___x_1720_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__12_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12,
    );
    v_time_1721_ = lean_int_mul(v_days_1719_, v___x_1720_);
    if v_leap_1712_ == 0 {
        leanh::lean_dec(v_a_1717_);
        return v_time_1721_;
    } else {
        let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: u8 = 0;
        v___x_1722_ = leanh::lean_unsigned_to_nat(2);
        v___x_1723_ = lean_nat_dec_le(v___x_1722_, v_a_1717_);
        leanh::lean_dec(v_a_1717_);
        if v___x_1723_ == 0 {
            return v_time_1721_;
        } else {
            let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1724_ = lean_int_add(v_time_1721_, v___x_1720_);
            leanh::lean_dec(v_time_1721_);
            return v___x_1724_;
        }
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_toSeconds___boxed(
    mut v_leap_1725_: *mut leanh::LeanObject,
    mut v_month_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_1727_: u8 = 0;
    let mut v_res_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1727_ = (leanh::lean_unbox(v_leap_1725_) as u8);
    v_res_1728_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_boxed_1727_, v_month_1726_);
    leanh::lean_dec(v_month_1726_);
    return v_res_1728_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__0(
    mut v_a_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = lean_nat_to_int(v_a_1729_);
    v___x_1731_ = l_Rat_ofInt(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = leanh::lean_unsigned_to_nat(60);
    v___x_1733_ = lean_nat_to_int(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toMinutes(
    mut v_leap_1734_: u8,
    mut v_month_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_1734_, v_month_1735_);
    v___x_1737_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0,
    );
    v___x_1738_ = lean_int_div(v___x_1736_, v___x_1737_);
    leanh::lean_dec(v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toMinutes___boxed(
    mut v_leap_1739_: *mut leanh::LeanObject,
    mut v_month_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_1741_: u8 = 0;
    let mut v_res_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1741_ = (leanh::lean_unbox(v_leap_1739_) as u8);
    v_res_1742_ = l_Std_Time_Month_Ordinal_toMinutes(v_leap_boxed_1741_, v_month_1740_);
    leanh::lean_dec(v_month_1740_);
    return v_res_1742_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toHours(
    mut v_leap_1743_: u8,
    mut v_month_1744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_1743_, v_month_1744_);
    v___x_1746_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0,
    );
    v___x_1747_ = lean_int_div(v___x_1745_, v___x_1746_);
    leanh::lean_dec(v___x_1745_);
    v___x_1748_ = lean_int_div(v___x_1747_, v___x_1746_);
    leanh::lean_dec(v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toHours___boxed(
    mut v_leap_1749_: *mut leanh::LeanObject,
    mut v_month_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_1751_: u8 = 0;
    let mut v_res_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1751_ = (leanh::lean_unbox(v_leap_1749_) as u8);
    v_res_1752_ = l_Std_Time_Month_Ordinal_toHours(v_leap_boxed_1751_, v_month_1750_);
    leanh::lean_dec(v_month_1750_);
    return v_res_1752_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toDays___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = leanh::lean_unsigned_to_nat(1);
    v___x_1754_ = l_Rat_instNatCast___lam__0(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toDays___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = leanh::lean_unsigned_to_nat(86400);
    v___x_1756_ = l_Rat_instNatCast___lam__0(v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toDays___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratio_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_toDays___closed__1,
    );
    v___x_1758_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toDays___closed__0,
    );
    v_ratio_1759_ = l_Rat_div(v___x_1758_, v___x_1757_);
    return v_ratio_1759_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toDays(
    mut v_leap_1760_: u8,
    mut v_month_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ratio_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ratio_1762_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_toDays___closed__2,
    );
    v_num_1763_ = leanh::lean_ctor_get(v_ratio_1762_, 0);
    v_den_1764_ = leanh::lean_ctor_get(v_ratio_1762_, 1);
    v___x_1765_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_1760_, v_month_1761_);
    v___x_1766_ = lean_int_mul(v___x_1765_, v_num_1763_);
    leanh::lean_dec(v___x_1765_);
    leanh::lean_inc(v_den_1764_);
    v___x_1767_ = lean_nat_to_int(v_den_1764_);
    v___x_1768_ = lean_int_ediv(v___x_1766_, v___x_1767_);
    leanh::lean_dec(v___x_1767_);
    leanh::lean_dec(v___x_1766_);
    return v___x_1768_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toDays___boxed(
    mut v_leap_1769_: *mut leanh::LeanObject,
    mut v_month_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_1771_: u8 = 0;
    let mut v_res_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1771_ = (leanh::lean_unbox(v_leap_1769_) as u8);
    v_res_1772_ = l_Std_Time_Month_Ordinal_toDays(v_leap_boxed_1771_, v_month_1770_);
    leanh::lean_dec(v_month_1770_);
    return v_res_1772_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = leanh::lean_unsigned_to_nat(30);
    v___x_1774_ = lean_nat_to_int(v___x_1773_);
    return v___x_1774_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1775_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
    v___x_1776_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1777_ = lean_int_add(v___x_1776_, v___x_1775_);
    return v___x_1777_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = leanh::lean_unsigned_to_nat(31);
    v___x_1779_ = lean_nat_to_int(v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1781_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1);
    v___x_1782_ = lean_int_sub(v___x_1781_, v___x_1780_);
    return v___x_1782_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1784_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3);
    v_range_1785_ = lean_int_add(v___x_1784_, v___x_1783_);
    return v_range_1785_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
    v___x_1788_ = lean_int_sub(v___x_1787_, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6()
-> *mut leanh::LeanObject {
    let mut v_range_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1789_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1790_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5);
    v___x_1791_ = lean_int_emod(v___x_1790_, v_range_1789_);
    return v___x_1791_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7()
-> *mut leanh::LeanObject {
    let mut v_range_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1792_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1793_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6);
    v___x_1794_ = lean_int_add(v___x_1793_, v_range_1792_);
    return v___x_1794_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8()
-> *mut leanh::LeanObject {
    let mut v_range_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1795_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1796_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7);
    v___x_1797_ = lean_int_emod(v___x_1796_, v_range_1795_);
    return v___x_1797_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1799_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8);
    v___x_1800_ = lean_int_add(v___x_1799_, v___x_1798_);
    return v___x_1800_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = leanh::lean_unsigned_to_nat(28);
    v___x_1802_ = lean_nat_to_int(v___x_1801_);
    return v___x_1802_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1804_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10);
    v___x_1805_ = lean_int_sub(v___x_1804_, v___x_1803_);
    return v___x_1805_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12()
-> *mut leanh::LeanObject {
    let mut v_range_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1807_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11);
    v___x_1808_ = lean_int_emod(v___x_1807_, v_range_1806_);
    return v___x_1808_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13()
-> *mut leanh::LeanObject {
    let mut v_range_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1809_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12);
    v___x_1811_ = lean_int_add(v___x_1810_, v_range_1809_);
    return v___x_1811_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14()
-> *mut leanh::LeanObject {
    let mut v_range_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1813_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13);
    v___x_1814_ = lean_int_emod(v___x_1813_, v_range_1812_);
    return v___x_1814_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14);
    v___x_1817_ = lean_int_add(v___x_1816_, v___x_1815_);
    return v___x_1817_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
    v___x_1820_ = lean_int_sub(v___x_1819_, v___x_1818_);
    return v___x_1820_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17()
-> *mut leanh::LeanObject {
    let mut v_range_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1821_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1822_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16);
    v___x_1823_ = lean_int_emod(v___x_1822_, v_range_1821_);
    return v___x_1823_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18()
-> *mut leanh::LeanObject {
    let mut v_range_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1824_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1825_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17);
    v___x_1826_ = lean_int_add(v___x_1825_, v_range_1824_);
    return v___x_1826_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19()
-> *mut leanh::LeanObject {
    let mut v_range_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1827_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18);
    v___x_1829_ = lean_int_emod(v___x_1828_, v_range_1827_);
    return v___x_1829_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1831_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19);
    v___x_1832_ = lean_int_add(v___x_1831_, v___x_1830_);
    return v___x_1832_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20);
    v___x_1834_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15);
    v___x_1835_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9);
    v___x_1836_ = leanh::lean_unsigned_to_nat(12);
    v___x_1837_ = lean_mk_empty_array_with_capacity(v___x_1836_);
    v___x_1838_ = lean_array_push(v___x_1837_, v___x_1835_);
    v___x_1839_ = lean_array_push(v___x_1838_, v___x_1834_);
    v___x_1840_ = lean_array_push(v___x_1839_, v___x_1835_);
    v___x_1841_ = lean_array_push(v___x_1840_, v___x_1833_);
    v___x_1842_ = lean_array_push(v___x_1841_, v___x_1835_);
    v___x_1843_ = lean_array_push(v___x_1842_, v___x_1833_);
    v___x_1844_ = lean_array_push(v___x_1843_, v___x_1835_);
    v___x_1845_ = lean_array_push(v___x_1844_, v___x_1835_);
    v___x_1846_ = lean_array_push(v___x_1845_, v___x_1833_);
    v___x_1847_ = lean_array_push(v___x_1846_, v___x_1835_);
    v___x_1848_ = lean_array_push(v___x_1847_, v___x_1833_);
    v___x_1849_ = lean_array_push(v___x_1848_, v___x_1835_);
    return v___x_1849_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap()
-> *mut leanh::LeanObject {
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21);
    return v___x_1850_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = leanh::lean_unsigned_to_nat(0);
    v___x_1852_ = lean_nat_to_int(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = leanh::lean_unsigned_to_nat(59);
    v___x_1854_ = lean_nat_to_int(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = leanh::lean_unsigned_to_nat(90);
    v___x_1856_ = lean_nat_to_int(v___x_1855_);
    return v___x_1856_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = leanh::lean_unsigned_to_nat(120);
    v___x_1858_ = lean_nat_to_int(v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = leanh::lean_unsigned_to_nat(151);
    v___x_1860_ = lean_nat_to_int(v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_unsigned_to_nat(181);
    v___x_1862_ = lean_nat_to_int(v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = leanh::lean_unsigned_to_nat(212);
    v___x_1864_ = lean_nat_to_int(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = leanh::lean_unsigned_to_nat(243);
    v___x_1866_ = lean_nat_to_int(v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = leanh::lean_unsigned_to_nat(273);
    v___x_1868_ = lean_nat_to_int(v___x_1867_);
    return v___x_1868_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = leanh::lean_unsigned_to_nat(304);
    v___x_1870_ = lean_nat_to_int(v___x_1869_);
    return v___x_1870_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = leanh::lean_unsigned_to_nat(334);
    v___x_1872_ = lean_nat_to_int(v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10);
    v___x_1874_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9);
    v___x_1875_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8);
    v___x_1876_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7);
    v___x_1877_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6);
    v___x_1878_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5);
    v___x_1879_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4);
    v___x_1880_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3);
    v___x_1881_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2);
    v___x_1882_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1);
    v___x_1883_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
    v___x_1884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0);
    v___x_1885_ = leanh::lean_unsigned_to_nat(12);
    v___x_1886_ = lean_mk_empty_array_with_capacity(v___x_1885_);
    v___x_1887_ = lean_array_push(v___x_1886_, v___x_1884_);
    v___x_1888_ = lean_array_push(v___x_1887_, v___x_1883_);
    v___x_1889_ = lean_array_push(v___x_1888_, v___x_1882_);
    v___x_1890_ = lean_array_push(v___x_1889_, v___x_1881_);
    v___x_1891_ = lean_array_push(v___x_1890_, v___x_1880_);
    v___x_1892_ = lean_array_push(v___x_1891_, v___x_1879_);
    v___x_1893_ = lean_array_push(v___x_1892_, v___x_1878_);
    v___x_1894_ = lean_array_push(v___x_1893_, v___x_1877_);
    v___x_1895_ = lean_array_push(v___x_1894_, v___x_1876_);
    v___x_1896_ = lean_array_push(v___x_1895_, v___x_1875_);
    v___x_1897_ = lean_array_push(v___x_1896_, v___x_1874_);
    v___x_1898_ = lean_array_push(v___x_1897_, v___x_1873_);
    return v___x_1898_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes()
-> *mut leanh::LeanObject {
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11);
    return v___x_1899_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = leanh::lean_unsigned_to_nat(2);
    v___x_1901_ = lean_nat_to_int(v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = leanh::lean_unsigned_to_nat(30);
    v___x_1903_ = lean_nat_to_int(v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__1,
    );
    v___x_1905_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1906_ = lean_int_add(v___x_1905_, v___x_1904_);
    return v___x_1906_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1908_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__2,
    );
    v___x_1909_ = lean_int_sub(v___x_1908_, v___x_1907_);
    return v___x_1909_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1911_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__3,
    );
    v_range_1912_ = lean_int_add(v___x_1911_, v___x_1910_);
    return v_range_1912_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1914_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0,
    );
    v___x_1915_ = lean_int_sub(v___x_1914_, v___x_1913_);
    return v___x_1915_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__6() -> *mut leanh::LeanObject {
    let mut v_range_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1916_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1917_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__5,
    );
    v___x_1918_ = lean_int_emod(v___x_1917_, v_range_1916_);
    return v___x_1918_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__7() -> *mut leanh::LeanObject {
    let mut v_range_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1919_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1920_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__6_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__6,
    );
    v___x_1921_ = lean_int_add(v___x_1920_, v_range_1919_);
    return v___x_1921_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__8() -> *mut leanh::LeanObject {
    let mut v_range_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1922_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__7_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__7,
    );
    v___x_1924_ = lean_int_emod(v___x_1923_, v_range_1922_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1926_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__8_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__8,
    );
    v___x_1927_ = lean_int_add(v___x_1926_, v___x_1925_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = leanh::lean_unsigned_to_nat(28);
    v___x_1929_ = lean_nat_to_int(v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1931_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__10_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__10,
    );
    v___x_1932_ = lean_int_sub(v___x_1931_, v___x_1930_);
    return v___x_1932_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__12() -> *mut leanh::LeanObject {
    let mut v_range_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1933_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1934_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__11_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__11,
    );
    v___x_1935_ = lean_int_emod(v___x_1934_, v_range_1933_);
    return v___x_1935_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__13() -> *mut leanh::LeanObject {
    let mut v_range_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1936_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1937_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__12_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__12,
    );
    v___x_1938_ = lean_int_add(v___x_1937_, v_range_1936_);
    return v___x_1938_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__14() -> *mut leanh::LeanObject {
    let mut v_range_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1939_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1940_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__13_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__13,
    );
    v___x_1941_ = lean_int_emod(v___x_1940_, v_range_1939_);
    return v___x_1941_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1943_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__14_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__14,
    );
    v___x_1944_ = lean_int_add(v___x_1943_, v___x_1942_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1946_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__1,
    );
    v___x_1947_ = lean_int_sub(v___x_1946_, v___x_1945_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__17() -> *mut leanh::LeanObject {
    let mut v_range_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1948_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1949_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__16_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__16,
    );
    v___x_1950_ = lean_int_emod(v___x_1949_, v_range_1948_);
    return v___x_1950_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__18() -> *mut leanh::LeanObject {
    let mut v_range_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1951_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1952_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__17_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__17,
    );
    v___x_1953_ = lean_int_add(v___x_1952_, v_range_1951_);
    return v___x_1953_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__19() -> *mut leanh::LeanObject {
    let mut v_range_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1954_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1955_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__18_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__18,
    );
    v___x_1956_ = lean_int_emod(v___x_1955_, v_range_1954_);
    return v___x_1956_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1957_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1958_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__19_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__19,
    );
    v___x_1959_ = lean_int_add(v___x_1958_, v___x_1957_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__20_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__20,
    );
    v___x_1961_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__15,
    );
    v___x_1962_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__9_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__9,
    );
    v___x_1963_ = leanh::lean_unsigned_to_nat(12);
    v___x_1964_ = lean_mk_empty_array_with_capacity(v___x_1963_);
    v___x_1965_ = lean_array_push(v___x_1964_, v___x_1962_);
    v___x_1966_ = lean_array_push(v___x_1965_, v___x_1961_);
    v___x_1967_ = lean_array_push(v___x_1966_, v___x_1962_);
    v___x_1968_ = lean_array_push(v___x_1967_, v___x_1960_);
    v___x_1969_ = lean_array_push(v___x_1968_, v___x_1962_);
    v___x_1970_ = lean_array_push(v___x_1969_, v___x_1960_);
    v___x_1971_ = lean_array_push(v___x_1970_, v___x_1962_);
    v___x_1972_ = lean_array_push(v___x_1971_, v___x_1962_);
    v___x_1973_ = lean_array_push(v___x_1972_, v___x_1960_);
    v___x_1974_ = lean_array_push(v___x_1973_, v___x_1962_);
    v___x_1975_ = lean_array_push(v___x_1974_, v___x_1960_);
    v___x_1976_ = lean_array_push(v___x_1975_, v___x_1962_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = leanh::lean_unsigned_to_nat(29);
    v___x_1978_ = lean_nat_to_int(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1980_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__22_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__22,
    );
    v___x_1981_ = lean_int_sub(v___x_1980_, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__24() -> *mut leanh::LeanObject {
    let mut v_range_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1982_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__23_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__23,
    );
    v___x_1984_ = lean_int_emod(v___x_1983_, v_range_1982_);
    return v___x_1984_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__25() -> *mut leanh::LeanObject {
    let mut v_range_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1985_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1986_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__24_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__24,
    );
    v___x_1987_ = lean_int_add(v___x_1986_, v_range_1985_);
    return v___x_1987_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__26() -> *mut leanh::LeanObject {
    let mut v_range_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_1988_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1989_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__25_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__25,
    );
    v___x_1990_ = lean_int_emod(v___x_1989_, v_range_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1992_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__26_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__26,
    );
    v___x_1993_ = lean_int_add(v___x_1992_, v___x_1991_);
    return v___x_1993_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_days(
    mut v_leap_1994_: u8,
    mut v_month_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    v___x_1996_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__0,
    );
    v___x_1997_ = lean_int_dec_eq(v_month_1995_, v___x_1996_);
    if v___x_1997_ == 0 {
        let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1998_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__21),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__21_once),
            _init_l_Std_Time_Month_Ordinal_days___closed__21,
        );
        v___x_1999_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1_once),
            _init_l_Std_Time_Month_Quarter_ofMonth___closed__1,
        );
        v___x_2000_ = lean_int_add(v_month_1995_, v___x_1999_);
        v___x_2001_ = l_Int_toNat(v___x_2000_);
        leanh::lean_dec(v___x_2000_);
        v___x_2002_ = lean_array_fget_borrowed(v___x_1998_, v___x_2001_);
        leanh::lean_dec(v___x_2001_);
        leanh::lean_inc(v___x_2002_);
        return v___x_2002_;
    } else {
        if v_leap_1994_ == 0 {
            let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2003_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15),
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15_once),
                _init_l_Std_Time_Month_Ordinal_days___closed__15,
            );
            return v___x_2003_;
        } else {
            let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2004_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__27),
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__27_once),
                _init_l_Std_Time_Month_Ordinal_days___closed__27,
            );
            return v___x_2004_;
        }
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_days___boxed(
    mut v_leap_2005_: *mut leanh::LeanObject,
    mut v_month_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_2007_: u8 = 0;
    let mut v_res_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_2007_ = (leanh::lean_unbox(v_leap_2005_) as u8);
    v_res_2008_ = l_Std_Time_Month_Ordinal_days(v_leap_boxed_2007_, v_month_2006_);
    leanh::lean_dec(v_month_2006_);
    return v_res_2008_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_cumulativeDays(
    mut v_leap_2009_: u8,
    mut v_month_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_2012_ = leanh::lean_unsigned_to_nat(12);
    v___x_2013_ = lean_mk_empty_array_with_capacity(v___x_2012_);
    leanh::lean_dec_ref(v___x_2013_);
    v___x_2014_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11,
    );
    v___x_2015_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_2016_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1_once),
        _init_l_Std_Time_Month_Quarter_ofMonth___closed__1,
    );
    v___x_2017_ = lean_int_add(v_month_2010_, v___x_2016_);
    v___x_2018_ = l_Int_toNat(v___x_2017_);
    leanh::lean_dec(v___x_2017_);
    v_res_2019_ = lean_array_fget_borrowed(v___x_2014_, v___x_2018_);
    leanh::lean_dec(v___x_2018_);
    if v_leap_2009_ == 0 {
        let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2020_ = lean_int_add(v_res_2019_, v___x_2011_);
        return v___x_2020_;
    } else {
        let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: u8 = 0;
        v___x_2021_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0_once),
            _init_l_Std_Time_Month_Ordinal_days___closed__0,
        );
        v___x_2022_ = lean_int_dec_lt(v___x_2021_, v_month_2010_);
        if v___x_2022_ == 0 {
            let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2023_ = lean_int_add(v_res_2019_, v___x_2011_);
            return v___x_2023_;
        } else {
            let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2024_ = lean_int_add(v_res_2019_, v___x_2015_);
            return v___x_2024_;
        }
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_cumulativeDays___boxed(
    mut v_leap_2025_: *mut leanh::LeanObject,
    mut v_month_2026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_2027_: u8 = 0;
    let mut v_res_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_2027_ = (leanh::lean_unbox(v_leap_2025_) as u8);
    v_res_2028_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_boxed_2027_, v_month_2026_);
    leanh::lean_dec(v_month_2026_);
    return v_res_2028_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_clipDay(
    mut v_leap_2029_: u8,
    mut v_month_2030_: *mut leanh::LeanObject,
    mut v_day_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_max_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    v_max_2032_ = l_Std_Time_Month_Ordinal_days(v_leap_2029_, v_month_2030_);
    v___x_2033_ = lean_int_dec_lt(v_max_2032_, v_day_2031_);
    if v___x_2033_ == 0 {
        leanh::lean_dec(v_max_2032_);
        leanh::lean_inc(v_day_2031_);
        return v_day_2031_;
    } else {
        return v_max_2032_;
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_clipDay___boxed(
    mut v_leap_2034_: *mut leanh::LeanObject,
    mut v_month_2035_: *mut leanh::LeanObject,
    mut v_day_2036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_2037_: u8 = 0;
    let mut v_res_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_2037_ = (leanh::lean_unbox(v_leap_2034_) as u8);
    v_res_2038_ = l_Std_Time_Month_Ordinal_clipDay(v_leap_boxed_2037_, v_month_2035_, v_day_2036_);
    leanh::lean_dec(v_day_2036_);
    leanh::lean_dec(v_month_2035_);
    return v_res_2038_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Month(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_Month_instLEOrdinal = _init_l_Std_Time_Month_instLEOrdinal();
    leanh::lean_mark_persistent(l_Std_Time_Month_instLEOrdinal);
    l_Std_Time_Month_instLTOrdinal = _init_l_Std_Time_Month_instLTOrdinal();
    leanh::lean_mark_persistent(l_Std_Time_Month_instLTOrdinal);
    l_Std_Time_Month_instInhabitedOrdinal = _init_l_Std_Time_Month_instInhabitedOrdinal();
    leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedOrdinal);
    l_Std_Time_Month_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Month_instInhabitedOffset___aux__1();
    leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedOffset___aux__1);
    l_Std_Time_Month_instInhabitedOffset = _init_l_Std_Time_Month_instInhabitedOffset();
    leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedOffset);
    l_Std_Time_Month_instLTOffset = _init_l_Std_Time_Month_instLTOffset();
    leanh::lean_mark_persistent(l_Std_Time_Month_instLTOffset);
    l_Std_Time_Month_instLEOffset = _init_l_Std_Time_Month_instLEOffset();
    leanh::lean_mark_persistent(l_Std_Time_Month_instLEOffset);
    l_Std_Time_Month_instLTQuarter = _init_l_Std_Time_Month_instLTQuarter();
    leanh::lean_mark_persistent(l_Std_Time_Month_instLTQuarter);
    l_Std_Time_Month_instLEQuarter = _init_l_Std_Time_Month_instLEQuarter();
    leanh::lean_mark_persistent(l_Std_Time_Month_instLEQuarter);
    l_Std_Time_Month_instInhabitedQuarter = _init_l_Std_Time_Month_instInhabitedQuarter();
    leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedQuarter);
    l_Std_Time_Month_Ordinal_january = _init_l_Std_Time_Month_Ordinal_january();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_january);
    l_Std_Time_Month_Ordinal_february = _init_l_Std_Time_Month_Ordinal_february();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_february);
    l_Std_Time_Month_Ordinal_march = _init_l_Std_Time_Month_Ordinal_march();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_march);
    l_Std_Time_Month_Ordinal_april = _init_l_Std_Time_Month_Ordinal_april();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_april);
    l_Std_Time_Month_Ordinal_may = _init_l_Std_Time_Month_Ordinal_may();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_may);
    l_Std_Time_Month_Ordinal_june = _init_l_Std_Time_Month_Ordinal_june();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_june);
    l_Std_Time_Month_Ordinal_july = _init_l_Std_Time_Month_Ordinal_july();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_july);
    l_Std_Time_Month_Ordinal_august = _init_l_Std_Time_Month_Ordinal_august();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_august);
    l_Std_Time_Month_Ordinal_september = _init_l_Std_Time_Month_Ordinal_september();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_september);
    l_Std_Time_Month_Ordinal_october = _init_l_Std_Time_Month_Ordinal_october();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_october);
    l_Std_Time_Month_Ordinal_november = _init_l_Std_Time_Month_Ordinal_november();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_november);
    l_Std_Time_Month_Ordinal_december = _init_l_Std_Time_Month_Ordinal_december();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_december);
    l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap =
        _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap();
    leanh::lean_mark_persistent(
        l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap,
    );
    l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes =
        _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes();
    leanh::lean_mark_persistent(
        l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Month(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Time_Month_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Month_Ordinal_ofNat___auto__1();
    leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_ofNat___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Unit_Month(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Day(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Month(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Month(builtin);
}