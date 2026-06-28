// Lean compiler output
// Module: Std.Time.Date.Unit.Month
// Imports: Std.Time.Date.Unit.Day Init.Data.Fin.Lemmas
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
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Std::Time::Date::Unit::Day::{
    initialize_Std_Time_Date_Unit_Day, l_Std_Time_Day_instInhabitedOffset,
    runtime_initialize_Std_Time_Date_Unit_Day,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{
    lean_int_div, lean_int_ediv, lean_int_emod,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le,
};
static mut l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instReprOrdinal___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instReprOrdinal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instReprOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instReprOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instLEOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instLTOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedOrdinal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instInhabitedOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instOrdOrdinal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instOrdOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instOrdOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instReprOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instInhabitedOffset___aux__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instInhabitedOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instAddOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Month_instAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_instSubOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Month_instSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_instMulOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instMulOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instMulOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instMulOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instMulOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_instDivOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_ediv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instDivOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instDivOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instDivOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instDivOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_instNegOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Month_instNegOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instNegOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_instToStringOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
static mut l_Std_Time_Month_instToStringOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instToStringOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instLTOffset: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Month_instLEOffset: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Month_instOrdOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instOrdOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instOrdOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instReprQuarter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instLTQuarter: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instLEQuarter: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_instInhabitedQuarter___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_instInhabitedQuarter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_instInhabitedQuarter: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_instOrdQuarter___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdQuarter___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Month_instOrdQuarter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdQuarter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Month_instOrdQuarter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_instOrdQuarter___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Month_Quarter_ofMonth___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Quarter_ofMonth___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Quarter_ofMonth___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Quarter_ofMonth___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_january: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_february___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_february___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_february: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_march___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_march___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_march: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_april___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_april___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_april: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_may___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_may___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_may: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_june___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_june___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_june: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_july___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_july___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_july: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_august___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_august___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_august: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_september___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_september___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_september: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_october___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_october___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_october: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_november___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_november___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_november: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_december___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_december___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_december: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14249328086033210933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value:
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
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Month_Ordinal_ofNat___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_ofFin___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_ofFin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toSeconds___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toDays___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toDays___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toDays___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toDays___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_toDays___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_toDays___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Month_Ordinal_days___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Month_Ordinal_days___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1021_ = lean_nat_to_int(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___aux__1(
    mut v_n_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    v___x_1024_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1025_ = lean_int_dec_lt(v_n_1022_, v___x_1024_);
    if v___x_1025_ == 0 {
        let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1026_ = l_Int_repr(v_n_1022_);
        v___x_1027_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
        return v___x_1027_;
    } else {
        let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1028_ = l_Int_repr(v_n_1022_);
        v___x_1029_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1029_, 0, v___x_1028_);
        v___x_1030_ = l_Repr_addAppParen(v___x_1029_, v_a_1023_);
        return v___x_1030_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___aux__1___boxed(
    mut v_n_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Std_Time_Month_instReprOrdinal___aux__1(v_n_1031_, v_a_1032_);
    crate::leanh::lean_dec(v_a_1032_);
    crate::leanh::lean_dec(v_n_1031_);
    return v_res_1033_;
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___lam__0(
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: u8 = 0;
    v___x_1036_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1037_ = lean_int_dec_lt(v___y_1034_, v___x_1036_);
    if v___x_1037_ == 0 {
        let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1038_ = l_Int_repr(v___y_1034_);
        v___x_1039_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1039_, 0, v___x_1038_);
        return v___x_1039_;
    } else {
        let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1040_ = l_Int_repr(v___y_1034_);
        v___x_1041_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1041_, 0, v___x_1040_);
        v___x_1042_ = l_Repr_addAppParen(v___x_1041_, v___y_1035_);
        return v___x_1042_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprOrdinal___lam__0___boxed(
    mut v___y_1043_: *mut crate::leanh::LeanObject,
    mut v___y_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Std_Time_Month_instReprOrdinal___lam__0(v___y_1043_, v___y_1044_);
    crate::leanh::lean_dec(v___y_1044_);
    crate::leanh::lean_dec(v___y_1043_);
    return v_res_1045_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal___aux__1(
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_b_1049_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1050_: u8 = 0;
    v___x_1050_ = lean_int_dec_eq(v_a_1048_, v_b_1049_);
    return v___x_1050_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_b_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1053_: u8 = 0;
    let mut v_r_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Std_Time_Month_instDecidableEqOrdinal___aux__1(v_a_1051_, v_b_1052_);
    crate::leanh::lean_dec(v_b_1052_);
    crate::leanh::lean_dec(v_a_1051_);
    v_r_1054_ = crate::leanh::lean_box((v_res_1053_) as usize);
    return v_r_1054_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal(
    mut v_a_1055_: *mut crate::leanh::LeanObject,
    mut v_b_1056_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1057_: u8 = 0;
    v___x_1057_ = lean_int_dec_eq(v_a_1055_, v_b_1056_);
    return v___x_1057_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOrdinal___boxed(
    mut v_a_1058_: *mut crate::leanh::LeanObject,
    mut v_b_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1060_: u8 = 0;
    let mut v_r_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Std_Time_Month_instDecidableEqOrdinal(v_a_1058_, v_b_1059_);
    crate::leanh::lean_dec(v_b_1059_);
    crate::leanh::lean_dec(v_a_1058_);
    v_r_1061_ = crate::leanh::lean_box((v_res_1060_) as usize);
    return v_r_1061_;
}
pub unsafe fn _init_l_Std_Time_Month_instLEOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = crate::leanh::lean_box(0);
    return v___x_1062_;
}
pub unsafe fn _init_l_Std_Time_Month_instLTOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = crate::leanh::lean_box(0);
    return v___x_1063_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1065_ = lean_nat_to_int(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1067_ = lean_nat_to_int(v___x_1066_);
    return v___x_1067_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_1069_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1070_ = lean_int_add(v___x_1069_, v___x_1068_);
    return v___x_1070_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1071_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__2,
    );
    v___x_1073_ = lean_int_sub(v___x_1072_, v___x_1071_);
    return v___x_1073_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1074_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1075_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__3,
    );
    v_range_1076_ = lean_int_add(v___x_1075_, v___x_1074_);
    return v_range_1076_;
}
pub unsafe fn l_Std_Time_Month_instOfNatOrdinal___aux__1(
    mut v_n_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1079_ = lean_nat_to_int(v_n_1077_);
    v_range_1080_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1081_ = lean_int_sub(v___x_1079_, v___x_1078_);
    crate::leanh::lean_dec(v___x_1079_);
    v___x_1082_ = lean_int_emod(v___x_1081_, v_range_1080_);
    crate::leanh::lean_dec(v___x_1081_);
    v___x_1083_ = lean_int_add(v___x_1082_, v_range_1080_);
    crate::leanh::lean_dec(v___x_1082_);
    v___x_1084_ = lean_int_emod(v___x_1083_, v_range_1080_);
    crate::leanh::lean_dec(v___x_1083_);
    v___x_1085_ = lean_int_add(v___x_1084_, v___x_1078_);
    crate::leanh::lean_dec(v___x_1084_);
    return v___x_1085_;
}
pub unsafe fn l_Std_Time_Month_instOfNatOrdinal(
    mut v_n_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1088_ = lean_nat_to_int(v_n_1086_);
    v_range_1089_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1090_ = lean_int_sub(v___x_1088_, v___x_1087_);
    crate::leanh::lean_dec(v___x_1088_);
    v___x_1091_ = lean_int_emod(v___x_1090_, v_range_1089_);
    crate::leanh::lean_dec(v___x_1090_);
    v___x_1092_ = lean_int_add(v___x_1091_, v_range_1089_);
    crate::leanh::lean_dec(v___x_1091_);
    v___x_1093_ = lean_int_emod(v___x_1092_, v_range_1089_);
    crate::leanh::lean_dec(v___x_1092_);
    v___x_1094_ = lean_int_add(v___x_1093_, v___x_1087_);
    crate::leanh::lean_dec(v___x_1093_);
    return v___x_1094_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1096_ = lean_int_sub(v___x_1095_, v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1097_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0,
    );
    v___x_1099_ = lean_int_emod(v___x_1098_, v_range_1097_);
    return v___x_1099_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1100_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1101_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__1,
    );
    v___x_1102_ = lean_int_add(v___x_1101_, v_range_1100_);
    return v___x_1102_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1103_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1104_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__2,
    );
    v___x_1105_ = lean_int_emod(v___x_1104_, v_range_1103_);
    return v___x_1105_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1107_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__3,
    );
    v___x_1108_ = lean_int_add(v___x_1107_, v___x_1106_);
    return v___x_1108_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4,
    );
    return v___x_1109_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal___aux__1(
    mut v_x_1110_: *mut crate::leanh::LeanObject,
    mut v_y_1111_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1112_: u8 = 0;
    v___x_1112_ = lean_int_dec_le(v_x_1110_, v_y_1111_);
    return v___x_1112_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_1113_: *mut crate::leanh::LeanObject,
    mut v_y_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1115_: u8 = 0;
    let mut v_r_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_Std_Time_Month_instDecidableLeOrdinal___aux__1(v_x_1113_, v_y_1114_);
    crate::leanh::lean_dec(v_y_1114_);
    crate::leanh::lean_dec(v_x_1113_);
    v_r_1116_ = crate::leanh::lean_box((v_res_1115_) as usize);
    return v_r_1116_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal(
    mut v___y_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1119_: u8 = 0;
    v___x_1119_ = lean_int_dec_le(v___y_1117_, v___y_1118_);
    return v___x_1119_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOrdinal___boxed(
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1122_: u8 = 0;
    let mut v_r_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Std_Time_Month_instDecidableLeOrdinal(v___y_1120_, v___y_1121_);
    crate::leanh::lean_dec(v___y_1121_);
    crate::leanh::lean_dec(v___y_1120_);
    v_r_1123_ = crate::leanh::lean_box((v_res_1122_) as usize);
    return v_r_1123_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal___aux__1(
    mut v_x_1124_: *mut crate::leanh::LeanObject,
    mut v_y_1125_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1126_: u8 = 0;
    v___x_1126_ = lean_int_dec_lt(v_x_1124_, v_y_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_1127_: *mut crate::leanh::LeanObject,
    mut v_y_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1129_: u8 = 0;
    let mut v_r_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Std_Time_Month_instDecidableLtOrdinal___aux__1(v_x_1127_, v_y_1128_);
    crate::leanh::lean_dec(v_y_1128_);
    crate::leanh::lean_dec(v_x_1127_);
    v_r_1130_ = crate::leanh::lean_box((v_res_1129_) as usize);
    return v_r_1130_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal(
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1133_: u8 = 0;
    v___x_1133_ = lean_int_dec_lt(v___y_1131_, v___y_1132_);
    return v___x_1133_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOrdinal___boxed(
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1136_: u8 = 0;
    let mut v_r_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l_Std_Time_Month_instDecidableLtOrdinal(v___y_1134_, v___y_1135_);
    crate::leanh::lean_dec(v___y_1135_);
    crate::leanh::lean_dec(v___y_1134_);
    v_r_1137_ = crate::leanh::lean_box((v_res_1136_) as usize);
    return v_r_1137_;
}
pub unsafe fn l_Std_Time_Month_instOrdOrdinal___aux__1(
    mut v_x_1138_: *mut crate::leanh::LeanObject,
    mut v_y_1139_: *mut crate::leanh::LeanObject,
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
    mut v_x_1145_: *mut crate::leanh::LeanObject,
    mut v_y_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1147_: u8 = 0;
    let mut v_r_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1147_ = l_Std_Time_Month_instOrdOrdinal___aux__1(v_x_1145_, v_y_1146_);
    crate::leanh::lean_dec(v_y_1146_);
    crate::leanh::lean_dec(v_x_1145_);
    v_r_1148_ = crate::leanh::lean_box((v_res_1147_) as usize);
    return v_r_1148_;
}
pub unsafe fn l_Std_Time_Month_instReprOffset___aux__1(
    mut v_i_1151_: *mut crate::leanh::LeanObject,
    mut v_prec_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    v___x_1153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1154_ = lean_int_dec_lt(v_i_1151_, v___x_1153_);
    if v___x_1154_ == 0 {
        let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1155_ = l_Int_repr(v_i_1151_);
        v___x_1156_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
        return v___x_1156_;
    } else {
        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1157_ = l_Int_repr(v_i_1151_);
        v___x_1158_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
        v___x_1159_ = l_Repr_addAppParen(v___x_1158_, v_prec_1152_);
        return v___x_1159_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprOffset___aux__1___boxed(
    mut v_i_1160_: *mut crate::leanh::LeanObject,
    mut v_prec_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_Time_Month_instReprOffset___aux__1(v_i_1160_, v_prec_1161_);
    crate::leanh::lean_dec(v_prec_1161_);
    crate::leanh::lean_dec(v_i_1160_);
    return v_res_1162_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset___aux__1(
    mut v_a_1164_: *mut crate::leanh::LeanObject,
    mut v_b_1165_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1166_: u8 = 0;
    v___x_1166_ = lean_int_dec_eq(v_a_1164_, v_b_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset___aux__1___boxed(
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_b_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1169_: u8 = 0;
    let mut v_r_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_Std_Time_Month_instDecidableEqOffset___aux__1(v_a_1167_, v_b_1168_);
    crate::leanh::lean_dec(v_b_1168_);
    crate::leanh::lean_dec(v_a_1167_);
    v_r_1170_ = crate::leanh::lean_box((v_res_1169_) as usize);
    return v_r_1170_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset(
    mut v_a_1171_: *mut crate::leanh::LeanObject,
    mut v_b_1172_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1173_: u8 = 0;
    v___x_1173_ = lean_int_dec_eq(v_a_1171_, v_b_1172_);
    return v___x_1173_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqOffset___boxed(
    mut v_a_1174_: *mut crate::leanh::LeanObject,
    mut v_b_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1176_: u8 = 0;
    let mut v_r_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Std_Time_Month_instDecidableEqOffset(v_a_1174_, v_b_1175_);
    crate::leanh::lean_dec(v_b_1175_);
    crate::leanh::lean_dec(v_a_1174_);
    v_r_1177_ = crate::leanh::lean_box((v_res_1176_) as usize);
    return v_r_1177_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOffset___aux__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    return v___x_1178_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    return v___x_1179_;
}
pub unsafe fn l_Std_Time_Month_instAddOffset___aux__1(
    mut v_m_1180_: *mut crate::leanh::LeanObject,
    mut v_n_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_int_add(v_m_1180_, v_n_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Std_Time_Month_instAddOffset___aux__1___boxed(
    mut v_m_1183_: *mut crate::leanh::LeanObject,
    mut v_n_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1185_ = l_Std_Time_Month_instAddOffset___aux__1(v_m_1183_, v_n_1184_);
    crate::leanh::lean_dec(v_n_1184_);
    crate::leanh::lean_dec(v_m_1183_);
    return v_res_1185_;
}
pub unsafe fn l_Std_Time_Month_instSubOffset___aux__1(
    mut v_m_1188_: *mut crate::leanh::LeanObject,
    mut v_n_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = lean_int_sub(v_m_1188_, v_n_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Std_Time_Month_instSubOffset___aux__1___boxed(
    mut v_m_1191_: *mut crate::leanh::LeanObject,
    mut v_n_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_Std_Time_Month_instSubOffset___aux__1(v_m_1191_, v_n_1192_);
    crate::leanh::lean_dec(v_n_1192_);
    crate::leanh::lean_dec(v_m_1191_);
    return v_res_1193_;
}
pub unsafe fn l_Std_Time_Month_instMulOffset___aux__1(
    mut v_m_1196_: *mut crate::leanh::LeanObject,
    mut v_n_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = lean_int_mul(v_m_1196_, v_n_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Std_Time_Month_instMulOffset___aux__1___boxed(
    mut v_m_1199_: *mut crate::leanh::LeanObject,
    mut v_n_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Std_Time_Month_instMulOffset___aux__1(v_m_1199_, v_n_1200_);
    crate::leanh::lean_dec(v_n_1200_);
    crate::leanh::lean_dec(v_m_1199_);
    return v_res_1201_;
}
pub unsafe fn l_Std_Time_Month_instDivOffset___aux__1(
    mut v_a_1204_: *mut crate::leanh::LeanObject,
    mut v_a_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = lean_int_ediv(v_a_1204_, v_a_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Std_Time_Month_instDivOffset___aux__1___boxed(
    mut v_a_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Std_Time_Month_instDivOffset___aux__1(v_a_1207_, v_a_1208_);
    crate::leanh::lean_dec(v_a_1208_);
    crate::leanh::lean_dec(v_a_1207_);
    return v_res_1209_;
}
pub unsafe fn l_Std_Time_Month_instNegOffset___aux__1(
    mut v_n_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = lean_int_neg(v_n_1212_);
    return v___x_1213_;
}
pub unsafe fn l_Std_Time_Month_instNegOffset___aux__1___boxed(
    mut v_n_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l_Std_Time_Month_instNegOffset___aux__1(v_n_1214_);
    crate::leanh::lean_dec(v_n_1214_);
    return v_res_1215_;
}
pub unsafe fn l_Std_Time_Month_instToStringOffset___aux__1(
    mut v_a_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Int_repr(v_a_1218_);
    return v___x_1219_;
}
pub unsafe fn l_Std_Time_Month_instToStringOffset___aux__1___boxed(
    mut v_a_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1221_ = l_Std_Time_Month_instToStringOffset___aux__1(v_a_1220_);
    crate::leanh::lean_dec(v_a_1220_);
    return v_res_1221_;
}
pub unsafe fn _init_l_Std_Time_Month_instLTOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1224_ = crate::leanh::lean_box(0);
    return v___x_1224_;
}
pub unsafe fn _init_l_Std_Time_Month_instLEOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1225_ = crate::leanh::lean_box(0);
    return v___x_1225_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOffset(
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1228_: u8 = 0;
    v___x_1228_ = lean_int_dec_le(v___y_1226_, v___y_1227_);
    return v___x_1228_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLeOffset___boxed(
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1231_: u8 = 0;
    let mut v_r_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_Std_Time_Month_instDecidableLeOffset(v___y_1229_, v___y_1230_);
    crate::leanh::lean_dec(v___y_1230_);
    crate::leanh::lean_dec(v___y_1229_);
    v_r_1232_ = crate::leanh::lean_box((v_res_1231_) as usize);
    return v_r_1232_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOffset(
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1235_: u8 = 0;
    v___x_1235_ = lean_int_dec_lt(v___y_1233_, v___y_1234_);
    return v___x_1235_;
}
pub unsafe fn l_Std_Time_Month_instDecidableLtOffset___boxed(
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1238_: u8 = 0;
    let mut v_r_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ = l_Std_Time_Month_instDecidableLtOffset(v___y_1236_, v___y_1237_);
    crate::leanh::lean_dec(v___y_1237_);
    crate::leanh::lean_dec(v___y_1236_);
    v_r_1239_ = crate::leanh::lean_box((v_res_1238_) as usize);
    return v_r_1239_;
}
pub unsafe fn l_Std_Time_Month_instOfNatOffset(
    mut v_n_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1241_ = lean_nat_to_int(v_n_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Std_Time_Month_instOrdOffset___aux__1(
    mut v_x_1242_: *mut crate::leanh::LeanObject,
    mut v_y_1243_: *mut crate::leanh::LeanObject,
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
    mut v_x_1249_: *mut crate::leanh::LeanObject,
    mut v_y_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: u8 = 0;
    let mut v_r_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Std_Time_Month_instOrdOffset___aux__1(v_x_1249_, v_y_1250_);
    crate::leanh::lean_dec(v_y_1250_);
    crate::leanh::lean_dec(v_x_1249_);
    v_r_1252_ = crate::leanh::lean_box((v_res_1251_) as usize);
    return v_r_1252_;
}
pub unsafe fn l_Std_Time_Month_instReprQuarter___aux__1(
    mut v_n_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: u8 = 0;
    v___x_1257_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1258_ = lean_int_dec_lt(v_n_1255_, v___x_1257_);
    if v___x_1258_ == 0 {
        let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1259_ = l_Int_repr(v_n_1255_);
        v___x_1260_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1260_, 0, v___x_1259_);
        return v___x_1260_;
    } else {
        let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1261_ = l_Int_repr(v_n_1255_);
        v___x_1262_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1262_, 0, v___x_1261_);
        v___x_1263_ = l_Repr_addAppParen(v___x_1262_, v_a_1256_);
        return v___x_1263_;
    }
}
pub unsafe fn l_Std_Time_Month_instReprQuarter___aux__1___boxed(
    mut v_n_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Std_Time_Month_instReprQuarter___aux__1(v_n_1264_, v_a_1265_);
    crate::leanh::lean_dec(v_a_1265_);
    crate::leanh::lean_dec(v_n_1264_);
    return v_res_1266_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter___aux__1(
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_b_1269_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1270_: u8 = 0;
    v___x_1270_ = lean_int_dec_eq(v_a_1268_, v_b_1269_);
    return v___x_1270_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter___aux__1___boxed(
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_b_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1273_: u8 = 0;
    let mut v_r_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Std_Time_Month_instDecidableEqQuarter___aux__1(v_a_1271_, v_b_1272_);
    crate::leanh::lean_dec(v_b_1272_);
    crate::leanh::lean_dec(v_a_1271_);
    v_r_1274_ = crate::leanh::lean_box((v_res_1273_) as usize);
    return v_r_1274_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter(
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_b_1276_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1277_: u8 = 0;
    v___x_1277_ = lean_int_dec_eq(v_a_1275_, v_b_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Std_Time_Month_instDecidableEqQuarter___boxed(
    mut v_a_1278_: *mut crate::leanh::LeanObject,
    mut v_b_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1280_: u8 = 0;
    let mut v_r_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Std_Time_Month_instDecidableEqQuarter(v_a_1278_, v_b_1279_);
    crate::leanh::lean_dec(v_b_1279_);
    crate::leanh::lean_dec(v_a_1278_);
    v_r_1281_ = crate::leanh::lean_box((v_res_1280_) as usize);
    return v_r_1281_;
}
pub unsafe fn _init_l_Std_Time_Month_instLTQuarter() -> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = crate::leanh::lean_box(0);
    return v___x_1282_;
}
pub unsafe fn _init_l_Std_Time_Month_instLEQuarter() -> *mut crate::leanh::LeanObject {
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = crate::leanh::lean_box(0);
    return v___x_1283_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1285_ = lean_nat_to_int(v___x_1284_);
    return v___x_1285_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0,
    );
    v___x_1287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1288_ = lean_int_add(v___x_1287_, v___x_1286_);
    return v___x_1288_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1290_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__1,
    );
    v___x_1291_ = lean_int_sub(v___x_1290_, v___x_1289_);
    return v___x_1291_;
}
pub unsafe fn _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1292_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__2,
    );
    v_range_1294_ = lean_int_add(v___x_1293_, v___x_1292_);
    return v_range_1294_;
}
pub unsafe fn l_Std_Time_Month_instOfNatQuarter___aux__1(
    mut v_n_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1296_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1297_ = lean_nat_to_int(v_n_1295_);
    v_range_1298_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1299_ = lean_int_sub(v___x_1297_, v___x_1296_);
    crate::leanh::lean_dec(v___x_1297_);
    v___x_1300_ = lean_int_emod(v___x_1299_, v_range_1298_);
    crate::leanh::lean_dec(v___x_1299_);
    v___x_1301_ = lean_int_add(v___x_1300_, v_range_1298_);
    crate::leanh::lean_dec(v___x_1300_);
    v___x_1302_ = lean_int_emod(v___x_1301_, v_range_1298_);
    crate::leanh::lean_dec(v___x_1301_);
    v___x_1303_ = lean_int_add(v___x_1302_, v___x_1296_);
    crate::leanh::lean_dec(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Std_Time_Month_instOfNatQuarter(
    mut v_n_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1306_ = lean_nat_to_int(v_n_1304_);
    v_range_1307_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1308_ = lean_int_sub(v___x_1306_, v___x_1305_);
    crate::leanh::lean_dec(v___x_1306_);
    v___x_1309_ = lean_int_emod(v___x_1308_, v_range_1307_);
    crate::leanh::lean_dec(v___x_1308_);
    v___x_1310_ = lean_int_add(v___x_1309_, v_range_1307_);
    crate::leanh::lean_dec(v___x_1309_);
    v___x_1311_ = lean_int_emod(v___x_1310_, v_range_1307_);
    crate::leanh::lean_dec(v___x_1310_);
    v___x_1312_ = lean_int_add(v___x_1311_, v___x_1305_);
    crate::leanh::lean_dec(v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1314_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__0,
    );
    v___x_1315_ = lean_int_emod(v___x_1314_, v_range_1313_);
    return v___x_1315_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1316_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1317_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__0_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__0,
    );
    v___x_1318_ = lean_int_add(v___x_1317_, v_range_1316_);
    return v___x_1318_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1319_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__3,
    );
    v___x_1320_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__1_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__1,
    );
    v___x_1321_ = lean_int_emod(v___x_1320_, v_range_1319_);
    return v___x_1321_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1323_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__2_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__2,
    );
    v___x_1324_ = lean_int_add(v___x_1323_, v___x_1322_);
    return v___x_1324_;
}
pub unsafe fn _init_l_Std_Time_Month_instInhabitedQuarter() -> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedQuarter___closed__3_once),
        _init_l_Std_Time_Month_instInhabitedQuarter___closed__3,
    );
    return v___x_1325_;
}
pub unsafe fn l_Std_Time_Month_instOrdQuarter___aux__1(
    mut v_x_1326_: *mut crate::leanh::LeanObject,
    mut v_y_1327_: *mut crate::leanh::LeanObject,
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
    mut v_x_1333_: *mut crate::leanh::LeanObject,
    mut v_y_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1335_: u8 = 0;
    let mut v_r_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1335_ = l_Std_Time_Month_instOrdQuarter___aux__1(v_x_1333_, v_y_1334_);
    crate::leanh::lean_dec(v_y_1334_);
    crate::leanh::lean_dec(v_x_1333_);
    v_r_1336_ = crate::leanh::lean_box((v_res_1335_) as usize);
    return v_r_1336_;
}
pub unsafe fn _init_l_Std_Time_Month_Quarter_ofMonth___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1340_ = lean_nat_to_int(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l_Std_Time_Month_Quarter_ofMonth___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1342_ = lean_int_neg(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn l_Std_Time_Month_Quarter_ofMonth(
    mut v_month_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1344_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1345_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__0_once),
        _init_l_Std_Time_Month_Quarter_ofMonth___closed__0,
    );
    v___x_1346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1_once),
        _init_l_Std_Time_Month_Quarter_ofMonth___closed__1,
    );
    v___x_1347_ = lean_int_add(v_month_1343_, v___x_1346_);
    v___x_1348_ = lean_int_ediv(v___x_1347_, v___x_1345_);
    crate::leanh::lean_dec(v___x_1347_);
    v___x_1349_ = lean_int_add(v___x_1348_, v___x_1344_);
    crate::leanh::lean_dec(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_Std_Time_Month_Quarter_ofMonth___boxed(
    mut v_month_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1351_ = l_Std_Time_Month_Quarter_ofMonth(v_month_1350_);
    crate::leanh::lean_dec(v_month_1350_);
    return v_res_1351_;
}
pub unsafe fn l_Std_Time_Month_Offset_ofNat(
    mut v_data_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = lean_nat_to_int(v_data_1352_);
    return v___x_1353_;
}
pub unsafe fn l_Std_Time_Month_Offset_ofInt(
    mut v_data_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_1354_);
    return v_data_1354_;
}
pub unsafe fn l_Std_Time_Month_Offset_ofInt___boxed(
    mut v_data_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_Std_Time_Month_Offset_ofInt(v_data_1355_);
    crate::leanh::lean_dec(v_data_1355_);
    return v_res_1356_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_january() -> *mut crate::leanh::LeanObject {
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Month_instInhabitedOrdinal___closed__4,
    );
    return v___x_1357_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1359_ = lean_nat_to_int(v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__0,
    );
    v___x_1362_ = lean_int_sub(v___x_1361_, v___x_1360_);
    return v___x_1362_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1364_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__1,
    );
    v___x_1365_ = lean_int_emod(v___x_1364_, v_range_1363_);
    return v___x_1365_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__2,
    );
    v___x_1368_ = lean_int_add(v___x_1367_, v_range_1366_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1370_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__3,
    );
    v___x_1371_ = lean_int_emod(v___x_1370_, v_range_1369_);
    return v___x_1371_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1373_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__4,
    );
    v___x_1374_ = lean_int_add(v___x_1373_, v___x_1372_);
    return v___x_1374_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_february() -> *mut crate::leanh::LeanObject {
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_february___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_february___closed__5,
    );
    return v___x_1375_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1377_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatQuarter___aux__1___closed__0,
    );
    v___x_1378_ = lean_int_sub(v___x_1377_, v___x_1376_);
    return v___x_1378_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v_range_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__0,
    );
    v___x_1381_ = lean_int_emod(v___x_1380_, v_range_1379_);
    return v___x_1381_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_range_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1382_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1383_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__1,
    );
    v___x_1384_ = lean_int_add(v___x_1383_, v_range_1382_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v_range_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1386_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__2,
    );
    v___x_1387_ = lean_int_emod(v___x_1386_, v_range_1385_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1389_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__3,
    );
    v___x_1390_ = lean_int_add(v___x_1389_, v___x_1388_);
    return v___x_1390_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_march() -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_march___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_march___closed__4,
    );
    return v___x_1391_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1393_ = lean_nat_to_int(v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1395_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__0,
    );
    v___x_1396_ = lean_int_sub(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_range_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1397_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__1,
    );
    v___x_1399_ = lean_int_emod(v___x_1398_, v_range_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v_range_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1400_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__2,
    );
    v___x_1402_ = lean_int_add(v___x_1401_, v_range_1400_);
    return v___x_1402_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1404_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__3,
    );
    v___x_1405_ = lean_int_emod(v___x_1404_, v_range_1403_);
    return v___x_1405_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1407_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__4,
    );
    v___x_1408_ = lean_int_add(v___x_1407_, v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_april() -> *mut crate::leanh::LeanObject {
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_april___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_april___closed__5,
    );
    return v___x_1409_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_1411_ = lean_nat_to_int(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__0,
    );
    v___x_1414_ = lean_int_sub(v___x_1413_, v___x_1412_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_range_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__1,
    );
    v___x_1417_ = lean_int_emod(v___x_1416_, v_range_1415_);
    return v___x_1417_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v_range_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__2,
    );
    v___x_1420_ = lean_int_add(v___x_1419_, v_range_1418_);
    return v___x_1420_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1421_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1422_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__3,
    );
    v___x_1423_ = lean_int_emod(v___x_1422_, v_range_1421_);
    return v___x_1423_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1425_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__4,
    );
    v___x_1426_ = lean_int_add(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_may() -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_may___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_may___closed__5,
    );
    return v___x_1427_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_1429_ = lean_nat_to_int(v___x_1428_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1431_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__0,
    );
    v___x_1432_ = lean_int_sub(v___x_1431_, v___x_1430_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_range_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__1,
    );
    v___x_1435_ = lean_int_emod(v___x_1434_, v_range_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v_range_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1436_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__2,
    );
    v___x_1438_ = lean_int_add(v___x_1437_, v_range_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1440_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__3,
    );
    v___x_1441_ = lean_int_emod(v___x_1440_, v_range_1439_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__4,
    );
    v___x_1444_ = lean_int_add(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_june() -> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_june___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_june___closed__5,
    );
    return v___x_1445_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_1447_ = lean_nat_to_int(v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1449_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__0,
    );
    v___x_1450_ = lean_int_sub(v___x_1449_, v___x_1448_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_range_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1451_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__1,
    );
    v___x_1453_ = lean_int_emod(v___x_1452_, v_range_1451_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v_range_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1454_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1455_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__2,
    );
    v___x_1456_ = lean_int_add(v___x_1455_, v_range_1454_);
    return v___x_1456_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1458_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__3,
    );
    v___x_1459_ = lean_int_emod(v___x_1458_, v_range_1457_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1461_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__4,
    );
    v___x_1462_ = lean_int_add(v___x_1461_, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_july() -> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_july___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_july___closed__5,
    );
    return v___x_1463_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_1465_ = lean_nat_to_int(v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1466_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1467_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__0,
    );
    v___x_1468_ = lean_int_sub(v___x_1467_, v___x_1466_);
    return v___x_1468_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_range_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1469_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1470_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__1,
    );
    v___x_1471_ = lean_int_emod(v___x_1470_, v_range_1469_);
    return v___x_1471_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v_range_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1472_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1473_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__2,
    );
    v___x_1474_ = lean_int_add(v___x_1473_, v_range_1472_);
    return v___x_1474_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1475_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1476_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__3,
    );
    v___x_1477_ = lean_int_emod(v___x_1476_, v_range_1475_);
    return v___x_1477_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1479_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__4,
    );
    v___x_1480_ = lean_int_add(v___x_1479_, v___x_1478_);
    return v___x_1480_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_august() -> *mut crate::leanh::LeanObject {
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_august___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_august___closed__5,
    );
    return v___x_1481_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1482_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1483_ = lean_nat_to_int(v___x_1482_);
    return v___x_1483_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1485_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__0,
    );
    v___x_1486_ = lean_int_sub(v___x_1485_, v___x_1484_);
    return v___x_1486_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1487_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1488_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__1,
    );
    v___x_1489_ = lean_int_emod(v___x_1488_, v_range_1487_);
    return v___x_1489_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1491_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__2,
    );
    v___x_1492_ = lean_int_add(v___x_1491_, v_range_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1493_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__3,
    );
    v___x_1495_ = lean_int_emod(v___x_1494_, v_range_1493_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__4,
    );
    v___x_1498_ = lean_int_add(v___x_1497_, v___x_1496_);
    return v___x_1498_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_september() -> *mut crate::leanh::LeanObject {
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_september___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_september___closed__5,
    );
    return v___x_1499_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1501_ = lean_nat_to_int(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__0,
    );
    v___x_1504_ = lean_int_sub(v___x_1503_, v___x_1502_);
    return v___x_1504_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1505_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1506_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__1,
    );
    v___x_1507_ = lean_int_emod(v___x_1506_, v_range_1505_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1508_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__2,
    );
    v___x_1510_ = lean_int_add(v___x_1509_, v_range_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__3,
    );
    v___x_1513_ = lean_int_emod(v___x_1512_, v_range_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__4,
    );
    v___x_1516_ = lean_int_add(v___x_1515_, v___x_1514_);
    return v___x_1516_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_october() -> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_october___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_october___closed__5,
    );
    return v___x_1517_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1519_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_1520_ = lean_int_sub(v___x_1519_, v___x_1518_);
    return v___x_1520_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1521_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1522_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__0,
    );
    v___x_1523_ = lean_int_emod(v___x_1522_, v_range_1521_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1525_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__1,
    );
    v___x_1526_ = lean_int_add(v___x_1525_, v_range_1524_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__2,
    );
    v___x_1529_ = lean_int_emod(v___x_1528_, v_range_1527_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__3,
    );
    v___x_1532_ = lean_int_add(v___x_1531_, v___x_1530_);
    return v___x_1532_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_november() -> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_november___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_november___closed__4,
    );
    return v___x_1533_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_1535_ = lean_nat_to_int(v___x_1534_);
    return v___x_1535_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__0,
    );
    v___x_1538_ = lean_int_sub(v___x_1537_, v___x_1536_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__1,
    );
    v___x_1541_ = lean_int_emod(v___x_1540_, v_range_1539_);
    return v___x_1541_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__2,
    );
    v___x_1544_ = lean_int_add(v___x_1543_, v_range_1542_);
    return v___x_1544_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1545_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_1546_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__3,
    );
    v___x_1547_ = lean_int_emod(v___x_1546_, v_range_1545_);
    return v___x_1547_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1549_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__4,
    );
    v___x_1550_ = lean_int_add(v___x_1549_, v___x_1548_);
    return v___x_1550_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_december() -> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_december___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_december___closed__5,
    );
    return v___x_1551_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toOffset(
    mut v_month_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_month_1552_);
    return v_month_1552_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toOffset___boxed(
    mut v_month_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Std_Time_Month_Ordinal_toOffset(v_month_1553_);
    crate::leanh::lean_dec(v_month_1553_);
    return v_res_1554_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt___redArg(
    mut v_data_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_1555_);
    return v_data_1555_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt___redArg___boxed(
    mut v_data_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l_Std_Time_Month_Ordinal_ofInt___redArg(v_data_1556_);
    crate::leanh::lean_dec(v_data_1556_);
    return v_res_1557_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt(
    mut v_data_1558_: *mut crate::leanh::LeanObject,
    mut v_h_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_1558_);
    return v_data_1558_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofInt___boxed(
    mut v_data_1560_: *mut crate::leanh::LeanObject,
    mut v_h_1561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1562_ = l_Std_Time_Month_Ordinal_ofInt(v_data_1560_, v_h_1561_);
    crate::leanh::lean_dec(v_data_1560_);
    return v_res_1562_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__10;
    v___x_1590_ = l_Lean_mkAtom(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__12,
    );
    v___x_1592_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1593_ = lean_array_push(v___x_1592_, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__16;
    v___x_1605_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1606_ = lean_array_push(v___x_1605_, v___x_1604_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__17,
    );
    v___x_1608_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__15;
    v___x_1609_ = crate::leanh::lean_box(2);
    v___x_1610_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    crate::leanh::lean_ctor_set(v___x_1610_, 1, v___x_1608_);
    crate::leanh::lean_ctor_set(v___x_1610_, 2, v___x_1607_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__18,
    );
    v___x_1612_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__13,
    );
    v___x_1613_ = lean_array_push(v___x_1612_, v___x_1611_);
    return v___x_1613_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__19,
    );
    v___x_1615_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__11;
    v___x_1616_ = crate::leanh::lean_box(2);
    v___x_1617_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
    crate::leanh::lean_ctor_set(v___x_1617_, 1, v___x_1615_);
    crate::leanh::lean_ctor_set(v___x_1617_, 2, v___x_1614_);
    return v___x_1617_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__20,
    );
    v___x_1619_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1620_ = lean_array_push(v___x_1619_, v___x_1618_);
    return v___x_1620_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__21,
    );
    v___x_1622_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__9;
    v___x_1623_ = crate::leanh::lean_box(2);
    v___x_1624_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1624_, 0, v___x_1623_);
    crate::leanh::lean_ctor_set(v___x_1624_, 1, v___x_1622_);
    crate::leanh::lean_ctor_set(v___x_1624_, 2, v___x_1621_);
    return v___x_1624_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__22,
    );
    v___x_1626_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1627_ = lean_array_push(v___x_1626_, v___x_1625_);
    return v___x_1627_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__23,
    );
    v___x_1629_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__7;
    v___x_1630_ = crate::leanh::lean_box(2);
    v___x_1631_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1631_, 0, v___x_1630_);
    crate::leanh::lean_ctor_set(v___x_1631_, 1, v___x_1629_);
    crate::leanh::lean_ctor_set(v___x_1631_, 2, v___x_1628_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__24,
    );
    v___x_1633_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__5;
    v___x_1634_ = lean_array_push(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__25,
    );
    v___x_1636_ = l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__4;
    v___x_1637_ = crate::leanh::lean_box(2);
    v___x_1638_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    crate::leanh::lean_ctor_set(v___x_1638_, 1, v___x_1636_);
    crate::leanh::lean_ctor_set(v___x_1638_, 2, v___x_1635_);
    return v___x_1638_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofNat___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26_once),
        _init_l_Std_Time_Month_Ordinal_ofNat___auto__1___closed__26,
    );
    return v___x_1639_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofNat___redArg(
    mut v_data_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1641_ = lean_nat_to_int(v_data_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofNat(
    mut v_data_1642_: *mut crate::leanh::LeanObject,
    mut v_h_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = lean_nat_to_int(v_data_1642_);
    return v___x_1644_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toNat(
    mut v_month_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1647_: u8 = 0;
    let mut v_a_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_intZero_1646_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v_isNeg_1647_ = lean_int_dec_lt(v_month_1645_, v_intZero_1646_);
    v_a_1648_ = lean_nat_abs(v_month_1645_);
    return v_a_1648_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toNat___boxed(
    mut v_month_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1650_ = l_Std_Time_Month_Ordinal_toNat(v_month_1649_);
    crate::leanh::lean_dec(v_month_1649_);
    return v_res_1650_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_ofFin___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1652_ = lean_nat_to_int(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_ofFin(
    mut v_data_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    v___x_1654_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1655_ = lean_nat_dec_le(v___x_1654_, v_data_1653_);
    if v___x_1655_ == 0 {
        let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_data_1653_);
        v___x_1656_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofFin___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_ofFin___closed__0_once),
            _init_l_Std_Time_Month_Ordinal_ofFin___closed__0,
        );
        return v___x_1656_;
    } else {
        let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1657_ = lean_nat_to_int(v_data_1653_);
        return v___x_1657_;
    }
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__1(
    mut v_a_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_nat_to_int(v_a_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__2(
    mut v_a_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Rat_ofInt(v_a_1660_);
    return v___x_1661_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_1663_ = lean_nat_to_int(v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_1665_ = lean_nat_to_int(v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = crate::leanh::lean_unsigned_to_nat(90);
    v___x_1667_ = lean_nat_to_int(v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = crate::leanh::lean_unsigned_to_nat(120);
    v___x_1669_ = lean_nat_to_int(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1670_ = crate::leanh::lean_unsigned_to_nat(151);
    v___x_1671_ = lean_nat_to_int(v___x_1670_);
    return v___x_1671_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1672_ = crate::leanh::lean_unsigned_to_nat(181);
    v___x_1673_ = lean_nat_to_int(v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = crate::leanh::lean_unsigned_to_nat(212);
    v___x_1675_ = lean_nat_to_int(v___x_1674_);
    return v___x_1675_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = crate::leanh::lean_unsigned_to_nat(243);
    v___x_1677_ = lean_nat_to_int(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = crate::leanh::lean_unsigned_to_nat(273);
    v___x_1679_ = lean_nat_to_int(v___x_1678_);
    return v___x_1679_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = crate::leanh::lean_unsigned_to_nat(304);
    v___x_1681_ = lean_nat_to_int(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ = crate::leanh::lean_unsigned_to_nat(334);
    v___x_1683_ = lean_nat_to_int(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysAcc_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__10_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__10,
    );
    v___x_1685_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__9_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__9,
    );
    v___x_1686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__8_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__8,
    );
    v___x_1687_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__7_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__7,
    );
    v___x_1688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__6_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__6,
    );
    v___x_1689_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__5,
    );
    v___x_1690_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__4,
    );
    v___x_1691_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__3,
    );
    v___x_1692_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__2,
    );
    v___x_1693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__1,
    );
    v___x_1694_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0,
    );
    v_intZero_1695_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_1696_ = crate::leanh::lean_unsigned_to_nat(12);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_1711_ = lean_nat_to_int(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toSeconds(
    mut v_leap_1712_: u8,
    mut v_month_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysAcc_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_days_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_intZero_1714_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v_isNeg_1715_ = lean_int_dec_lt(v_month_1713_, v_intZero_1714_);
    v___x_1716_ = l_Std_Time_Day_instInhabitedOffset;
    v_a_1717_ = lean_nat_abs(v_month_1713_);
    v_daysAcc_1718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11,
    );
    v_days_1719_ = lean_array_get_borrowed(v___x_1716_, v_daysAcc_1718_, v_a_1717_);
    v___x_1720_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__12_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__12,
    );
    v_time_1721_ = lean_int_mul(v_days_1719_, v___x_1720_);
    if v_leap_1712_ == 0 {
        crate::leanh::lean_dec(v_a_1717_);
        return v_time_1721_;
    } else {
        let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: u8 = 0;
        v___x_1722_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1723_ = lean_nat_dec_le(v___x_1722_, v_a_1717_);
        crate::leanh::lean_dec(v_a_1717_);
        if v___x_1723_ == 0 {
            return v_time_1721_;
        } else {
            let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1724_ = lean_int_add(v_time_1721_, v___x_1720_);
            crate::leanh::lean_dec(v_time_1721_);
            return v___x_1724_;
        }
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_toSeconds___boxed(
    mut v_leap_1725_: *mut crate::leanh::LeanObject,
    mut v_month_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1727_: u8 = 0;
    let mut v_res_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1727_ = (crate::leanh::lean_unbox(v_leap_1725_) as u8);
    v_res_1728_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_boxed_1727_, v_month_1726_);
    crate::leanh::lean_dec(v_month_1726_);
    return v_res_1728_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Month_Ordinal_toSeconds_spec__0(
    mut v_a_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = lean_nat_to_int(v_a_1729_);
    v___x_1731_ = l_Rat_ofInt(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_1733_ = lean_nat_to_int(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toMinutes(
    mut v_leap_1734_: u8,
    mut v_month_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_1734_, v_month_1735_);
    v___x_1737_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0,
    );
    v___x_1738_ = lean_int_div(v___x_1736_, v___x_1737_);
    crate::leanh::lean_dec(v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toMinutes___boxed(
    mut v_leap_1739_: *mut crate::leanh::LeanObject,
    mut v_month_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1741_: u8 = 0;
    let mut v_res_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1741_ = (crate::leanh::lean_unbox(v_leap_1739_) as u8);
    v_res_1742_ = l_Std_Time_Month_Ordinal_toMinutes(v_leap_boxed_1741_, v_month_1740_);
    crate::leanh::lean_dec(v_month_1740_);
    return v_res_1742_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toHours(
    mut v_leap_1743_: u8,
    mut v_month_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_1743_, v_month_1744_);
    v___x_1746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toMinutes___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toMinutes___closed__0,
    );
    v___x_1747_ = lean_int_div(v___x_1745_, v___x_1746_);
    crate::leanh::lean_dec(v___x_1745_);
    v___x_1748_ = lean_int_div(v___x_1747_, v___x_1746_);
    crate::leanh::lean_dec(v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toHours___boxed(
    mut v_leap_1749_: *mut crate::leanh::LeanObject,
    mut v_month_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1751_: u8 = 0;
    let mut v_res_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1751_ = (crate::leanh::lean_unbox(v_leap_1749_) as u8);
    v_res_1752_ = l_Std_Time_Month_Ordinal_toHours(v_leap_boxed_1751_, v_month_1750_);
    crate::leanh::lean_dec(v_month_1750_);
    return v_res_1752_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toDays___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1754_ = l_Rat_instNatCast___lam__0(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toDays___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_1756_ = l_Rat_instNatCast___lam__0(v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_toDays___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratio_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_toDays___closed__1,
    );
    v___x_1758_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toDays___closed__0,
    );
    v_ratio_1759_ = l_Rat_div(v___x_1758_, v___x_1757_);
    return v_ratio_1759_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toDays(
    mut v_leap_1760_: u8,
    mut v_month_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ratio_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ratio_1762_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toDays___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_toDays___closed__2,
    );
    v_num_1763_ = crate::leanh::lean_ctor_get(v_ratio_1762_, 0);
    v_den_1764_ = crate::leanh::lean_ctor_get(v_ratio_1762_, 1);
    v___x_1765_ = l_Std_Time_Month_Ordinal_toSeconds(v_leap_1760_, v_month_1761_);
    v___x_1766_ = lean_int_mul(v___x_1765_, v_num_1763_);
    crate::leanh::lean_dec(v___x_1765_);
    crate::leanh::lean_inc(v_den_1764_);
    v___x_1767_ = lean_nat_to_int(v_den_1764_);
    v___x_1768_ = lean_int_ediv(v___x_1766_, v___x_1767_);
    crate::leanh::lean_dec(v___x_1767_);
    crate::leanh::lean_dec(v___x_1766_);
    return v___x_1768_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_toDays___boxed(
    mut v_leap_1769_: *mut crate::leanh::LeanObject,
    mut v_month_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1771_: u8 = 0;
    let mut v_res_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1771_ = (crate::leanh::lean_unbox(v_leap_1769_) as u8);
    v_res_1772_ = l_Std_Time_Month_Ordinal_toDays(v_leap_boxed_1771_, v_month_1770_);
    crate::leanh::lean_dec(v_month_1770_);
    return v_res_1772_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_1774_ = lean_nat_to_int(v___x_1773_);
    return v___x_1774_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1775_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
    v___x_1776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1777_ = lean_int_add(v___x_1776_, v___x_1775_);
    return v___x_1777_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_1779_ = lean_nat_to_int(v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1781_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__1);
    v___x_1782_ = lean_int_sub(v___x_1781_, v___x_1780_);
    return v___x_1782_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1784_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__3);
    v_range_1785_ = lean_int_add(v___x_1784_, v___x_1783_);
    return v_range_1785_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1787_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
    v___x_1788_ = lean_int_sub(v___x_1787_, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1789_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1790_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__5);
    v___x_1791_ = lean_int_emod(v___x_1790_, v_range_1789_);
    return v___x_1791_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1792_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1793_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__6);
    v___x_1794_ = lean_int_add(v___x_1793_, v_range_1792_);
    return v___x_1794_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1795_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__7);
    v___x_1797_ = lean_int_emod(v___x_1796_, v_range_1795_);
    return v___x_1797_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1799_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__8);
    v___x_1800_ = lean_int_add(v___x_1799_, v___x_1798_);
    return v___x_1800_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = crate::leanh::lean_unsigned_to_nat(28);
    v___x_1802_ = lean_nat_to_int(v___x_1801_);
    return v___x_1802_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__10);
    v___x_1805_ = lean_int_sub(v___x_1804_, v___x_1803_);
    return v___x_1805_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1807_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__11);
    v___x_1808_ = lean_int_emod(v___x_1807_, v_range_1806_);
    return v___x_1808_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__12);
    v___x_1811_ = lean_int_add(v___x_1810_, v_range_1809_);
    return v___x_1811_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1813_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__13);
    v___x_1814_ = lean_int_emod(v___x_1813_, v_range_1812_);
    return v___x_1814_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__14);
    v___x_1817_ = lean_int_add(v___x_1816_, v___x_1815_);
    return v___x_1817_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1818_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1819_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__0);
    v___x_1820_ = lean_int_sub(v___x_1819_, v___x_1818_);
    return v___x_1820_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1821_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__16);
    v___x_1823_ = lean_int_emod(v___x_1822_, v_range_1821_);
    return v___x_1823_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1824_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1825_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__17);
    v___x_1826_ = lean_int_add(v___x_1825_, v_range_1824_);
    return v___x_1826_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__4);
    v___x_1828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__18);
    v___x_1829_ = lean_int_emod(v___x_1828_, v_range_1827_);
    return v___x_1829_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1831_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__19);
    v___x_1832_ = lean_int_add(v___x_1831_, v___x_1830_);
    return v___x_1832_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__20);
    v___x_1834_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__15);
    v___x_1835_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__9);
    v___x_1836_ = crate::leanh::lean_unsigned_to_nat(12);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__21);
    return v___x_1850_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1852_ = lean_nat_to_int(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_1854_ = lean_nat_to_int(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = crate::leanh::lean_unsigned_to_nat(90);
    v___x_1856_ = lean_nat_to_int(v___x_1855_);
    return v___x_1856_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = crate::leanh::lean_unsigned_to_nat(120);
    v___x_1858_ = lean_nat_to_int(v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = crate::leanh::lean_unsigned_to_nat(151);
    v___x_1860_ = lean_nat_to_int(v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = crate::leanh::lean_unsigned_to_nat(181);
    v___x_1862_ = lean_nat_to_int(v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = crate::leanh::lean_unsigned_to_nat(212);
    v___x_1864_ = lean_nat_to_int(v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = crate::leanh::lean_unsigned_to_nat(243);
    v___x_1866_ = lean_nat_to_int(v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = crate::leanh::lean_unsigned_to_nat(273);
    v___x_1868_ = lean_nat_to_int(v___x_1867_);
    return v___x_1868_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = crate::leanh::lean_unsigned_to_nat(304);
    v___x_1870_ = lean_nat_to_int(v___x_1869_);
    return v___x_1870_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = crate::leanh::lean_unsigned_to_nat(334);
    v___x_1872_ = lean_nat_to_int(v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__10);
    v___x_1874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__9);
    v___x_1875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__8);
    v___x_1876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__7);
    v___x_1877_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__6);
    v___x_1878_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__5);
    v___x_1879_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__4);
    v___x_1880_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__3);
    v___x_1881_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__2);
    v___x_1882_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__1);
    v___x_1883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap___closed__2);
    v___x_1884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__0);
    v___x_1885_ = crate::leanh::lean_unsigned_to_nat(12);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11), core::ptr::addr_of_mut!(l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11_once), _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes___closed__11);
    return v___x_1899_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1901_ = lean_nat_to_int(v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_1903_ = lean_nat_to_int(v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__1,
    );
    v___x_1905_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1906_ = lean_int_add(v___x_1905_, v___x_1904_);
    return v___x_1906_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1908_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__2_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__2,
    );
    v___x_1909_ = lean_int_sub(v___x_1908_, v___x_1907_);
    return v___x_1909_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1911_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__3_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__3,
    );
    v_range_1912_ = lean_int_add(v___x_1911_, v___x_1910_);
    return v_range_1912_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__0,
    );
    v___x_1915_ = lean_int_sub(v___x_1914_, v___x_1913_);
    return v___x_1915_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v_range_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1916_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1917_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__5_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__5,
    );
    v___x_1918_ = lean_int_emod(v___x_1917_, v_range_1916_);
    return v___x_1918_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v_range_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__6_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__6,
    );
    v___x_1921_ = lean_int_add(v___x_1920_, v_range_1919_);
    return v___x_1921_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v_range_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1922_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1923_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__7_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__7,
    );
    v___x_1924_ = lean_int_emod(v___x_1923_, v_range_1922_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1926_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__8_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__8,
    );
    v___x_1927_ = lean_int_add(v___x_1926_, v___x_1925_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = crate::leanh::lean_unsigned_to_nat(28);
    v___x_1929_ = lean_nat_to_int(v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1931_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__10_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__10,
    );
    v___x_1932_ = lean_int_sub(v___x_1931_, v___x_1930_);
    return v___x_1932_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v_range_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1933_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__11_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__11,
    );
    v___x_1935_ = lean_int_emod(v___x_1934_, v_range_1933_);
    return v___x_1935_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v_range_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1936_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1937_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__12_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__12,
    );
    v___x_1938_ = lean_int_add(v___x_1937_, v_range_1936_);
    return v___x_1938_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v_range_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1939_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1940_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__13_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__13,
    );
    v___x_1941_ = lean_int_emod(v___x_1940_, v_range_1939_);
    return v___x_1941_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1943_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__14_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__14,
    );
    v___x_1944_ = lean_int_add(v___x_1943_, v___x_1942_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1946_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__1_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__1,
    );
    v___x_1947_ = lean_int_sub(v___x_1946_, v___x_1945_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v_range_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1949_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__16_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__16,
    );
    v___x_1950_ = lean_int_emod(v___x_1949_, v_range_1948_);
    return v___x_1950_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v_range_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1951_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1952_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__17_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__17,
    );
    v___x_1953_ = lean_int_add(v___x_1952_, v_range_1951_);
    return v___x_1953_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v_range_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1954_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1955_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__18_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__18,
    );
    v___x_1956_ = lean_int_emod(v___x_1955_, v_range_1954_);
    return v___x_1956_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1957_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1958_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__19_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__19,
    );
    v___x_1959_ = lean_int_add(v___x_1958_, v___x_1957_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__20_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__20,
    );
    v___x_1961_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__15,
    );
    v___x_1962_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__9_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__9,
    );
    v___x_1963_ = crate::leanh::lean_unsigned_to_nat(12);
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
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = crate::leanh::lean_unsigned_to_nat(29);
    v___x_1978_ = lean_nat_to_int(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1980_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__22_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__22,
    );
    v___x_1981_ = lean_int_sub(v___x_1980_, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v_range_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1982_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__23_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__23,
    );
    v___x_1984_ = lean_int_emod(v___x_1983_, v_range_1982_);
    return v___x_1984_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v_range_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1985_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1986_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__24_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__24,
    );
    v___x_1987_ = lean_int_add(v___x_1986_, v_range_1985_);
    return v___x_1987_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v_range_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1988_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__4_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__4,
    );
    v___x_1989_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__25_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__25,
    );
    v___x_1990_ = lean_int_emod(v___x_1989_, v_range_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l_Std_Time_Month_Ordinal_days___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1992_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__26_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__26,
    );
    v___x_1993_ = lean_int_add(v___x_1992_, v___x_1991_);
    return v___x_1993_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_days(
    mut v_leap_1994_: u8,
    mut v_month_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    v___x_1996_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0_once),
        _init_l_Std_Time_Month_Ordinal_days___closed__0,
    );
    v___x_1997_ = lean_int_dec_eq(v_month_1995_, v___x_1996_);
    if v___x_1997_ == 0 {
        let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1998_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__21),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__21_once),
            _init_l_Std_Time_Month_Ordinal_days___closed__21,
        );
        v___x_1999_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1_once),
            _init_l_Std_Time_Month_Quarter_ofMonth___closed__1,
        );
        v___x_2000_ = lean_int_add(v_month_1995_, v___x_1999_);
        v___x_2001_ = l_Int_toNat(v___x_2000_);
        crate::leanh::lean_dec(v___x_2000_);
        v___x_2002_ = lean_array_fget_borrowed(v___x_1998_, v___x_2001_);
        crate::leanh::lean_dec(v___x_2001_);
        crate::leanh::lean_inc(v___x_2002_);
        return v___x_2002_;
    } else {
        if v_leap_1994_ == 0 {
            let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2003_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15),
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__15_once),
                _init_l_Std_Time_Month_Ordinal_days___closed__15,
            );
            return v___x_2003_;
        } else {
            let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2004_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__27),
                core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__27_once),
                _init_l_Std_Time_Month_Ordinal_days___closed__27,
            );
            return v___x_2004_;
        }
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_days___boxed(
    mut v_leap_2005_: *mut crate::leanh::LeanObject,
    mut v_month_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_2007_: u8 = 0;
    let mut v_res_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_2007_ = (crate::leanh::lean_unbox(v_leap_2005_) as u8);
    v_res_2008_ = l_Std_Time_Month_Ordinal_days(v_leap_boxed_2007_, v_month_2006_);
    crate::leanh::lean_dec(v_month_2006_);
    return v_res_2008_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_cumulativeDays(
    mut v_leap_2009_: u8,
    mut v_month_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instReprOrdinal___aux__1___closed__0,
    );
    v___x_2012_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2013_ = lean_mk_empty_array_with_capacity(v___x_2012_);
    crate::leanh::lean_dec_ref(v___x_2013_);
    v___x_2014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_toSeconds___closed__11_once),
        _init_l_Std_Time_Month_Ordinal_toSeconds___closed__11,
    );
    v___x_2015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Month_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_2016_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Month_Quarter_ofMonth___closed__1_once),
        _init_l_Std_Time_Month_Quarter_ofMonth___closed__1,
    );
    v___x_2017_ = lean_int_add(v_month_2010_, v___x_2016_);
    v___x_2018_ = l_Int_toNat(v___x_2017_);
    crate::leanh::lean_dec(v___x_2017_);
    v_res_2019_ = lean_array_fget_borrowed(v___x_2014_, v___x_2018_);
    crate::leanh::lean_dec(v___x_2018_);
    if v_leap_2009_ == 0 {
        let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2020_ = lean_int_add(v_res_2019_, v___x_2011_);
        return v___x_2020_;
    } else {
        let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: u8 = 0;
        v___x_2021_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Month_Ordinal_days___closed__0_once),
            _init_l_Std_Time_Month_Ordinal_days___closed__0,
        );
        v___x_2022_ = lean_int_dec_lt(v___x_2021_, v_month_2010_);
        if v___x_2022_ == 0 {
            let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2023_ = lean_int_add(v_res_2019_, v___x_2011_);
            return v___x_2023_;
        } else {
            let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2024_ = lean_int_add(v_res_2019_, v___x_2015_);
            return v___x_2024_;
        }
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_cumulativeDays___boxed(
    mut v_leap_2025_: *mut crate::leanh::LeanObject,
    mut v_month_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_2027_: u8 = 0;
    let mut v_res_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_2027_ = (crate::leanh::lean_unbox(v_leap_2025_) as u8);
    v_res_2028_ = l_Std_Time_Month_Ordinal_cumulativeDays(v_leap_boxed_2027_, v_month_2026_);
    crate::leanh::lean_dec(v_month_2026_);
    return v_res_2028_;
}
pub unsafe fn l_Std_Time_Month_Ordinal_clipDay(
    mut v_leap_2029_: u8,
    mut v_month_2030_: *mut crate::leanh::LeanObject,
    mut v_day_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_max_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    v_max_2032_ = l_Std_Time_Month_Ordinal_days(v_leap_2029_, v_month_2030_);
    v___x_2033_ = lean_int_dec_lt(v_max_2032_, v_day_2031_);
    if v___x_2033_ == 0 {
        crate::leanh::lean_dec(v_max_2032_);
        crate::leanh::lean_inc(v_day_2031_);
        return v_day_2031_;
    } else {
        return v_max_2032_;
    }
}
pub unsafe fn l_Std_Time_Month_Ordinal_clipDay___boxed(
    mut v_leap_2034_: *mut crate::leanh::LeanObject,
    mut v_month_2035_: *mut crate::leanh::LeanObject,
    mut v_day_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_2037_: u8 = 0;
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_2037_ = (crate::leanh::lean_unbox(v_leap_2034_) as u8);
    v_res_2038_ = l_Std_Time_Month_Ordinal_clipDay(v_leap_boxed_2037_, v_month_2035_, v_day_2036_);
    crate::leanh::lean_dec(v_day_2036_);
    crate::leanh::lean_dec(v_month_2035_);
    return v_res_2038_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Month(
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
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_Month_instLEOrdinal = _init_l_Std_Time_Month_instLEOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instLEOrdinal);
    l_Std_Time_Month_instLTOrdinal = _init_l_Std_Time_Month_instLTOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instLTOrdinal);
    l_Std_Time_Month_instInhabitedOrdinal = _init_l_Std_Time_Month_instInhabitedOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedOrdinal);
    l_Std_Time_Month_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Month_instInhabitedOffset___aux__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedOffset___aux__1);
    l_Std_Time_Month_instInhabitedOffset = _init_l_Std_Time_Month_instInhabitedOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedOffset);
    l_Std_Time_Month_instLTOffset = _init_l_Std_Time_Month_instLTOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instLTOffset);
    l_Std_Time_Month_instLEOffset = _init_l_Std_Time_Month_instLEOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instLEOffset);
    l_Std_Time_Month_instLTQuarter = _init_l_Std_Time_Month_instLTQuarter();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instLTQuarter);
    l_Std_Time_Month_instLEQuarter = _init_l_Std_Time_Month_instLEQuarter();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instLEQuarter);
    l_Std_Time_Month_instInhabitedQuarter = _init_l_Std_Time_Month_instInhabitedQuarter();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_instInhabitedQuarter);
    l_Std_Time_Month_Ordinal_january = _init_l_Std_Time_Month_Ordinal_january();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_january);
    l_Std_Time_Month_Ordinal_february = _init_l_Std_Time_Month_Ordinal_february();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_february);
    l_Std_Time_Month_Ordinal_march = _init_l_Std_Time_Month_Ordinal_march();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_march);
    l_Std_Time_Month_Ordinal_april = _init_l_Std_Time_Month_Ordinal_april();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_april);
    l_Std_Time_Month_Ordinal_may = _init_l_Std_Time_Month_Ordinal_may();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_may);
    l_Std_Time_Month_Ordinal_june = _init_l_Std_Time_Month_Ordinal_june();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_june);
    l_Std_Time_Month_Ordinal_july = _init_l_Std_Time_Month_Ordinal_july();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_july);
    l_Std_Time_Month_Ordinal_august = _init_l_Std_Time_Month_Ordinal_august();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_august);
    l_Std_Time_Month_Ordinal_september = _init_l_Std_Time_Month_Ordinal_september();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_september);
    l_Std_Time_Month_Ordinal_october = _init_l_Std_Time_Month_Ordinal_october();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_october);
    l_Std_Time_Month_Ordinal_november = _init_l_Std_Time_Month_Ordinal_november();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_november);
    l_Std_Time_Month_Ordinal_december = _init_l_Std_Time_Month_Ordinal_december();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_december);
    l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap =
        _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap();
    crate::leanh::lean_mark_persistent(
        l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_monthSizesNonLeap,
    );
    l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes =
        _init_l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes();
    crate::leanh::lean_mark_persistent(
        l___private_Std_Time_Date_Unit_Month_0__Std_Time_Month_Ordinal_cumulativeSizes,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Month(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Time_Month_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Month_Ordinal_ofNat___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Month_Ordinal_ofNat___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Unit_Month(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Month(builtin);
}
