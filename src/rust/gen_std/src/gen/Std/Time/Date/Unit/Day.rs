// Lean compiler output
// Module: Std.Time.Date.Unit.Day
// Imports: Std.Time.Time
use crate::ffi::{
    lean_array_push, lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt,
    lean_int_ediv, lean_int_emod, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_dec_le,
    lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_instNatCast___lam__0, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::r#gen::Std::Time::Time::{initialize_Std_Time_Time, runtime_initialize_Std_Time_Time};
static mut l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instReprOrdinal___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Day_instReprOrdinal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Day_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Day_instReprOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instReprOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instLEOrdinal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Day_instLTOrdinal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOrdinal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Day_instInhabitedOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Day_instOrdOrdinal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Day_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Day_instOrdOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instOrdOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instReprOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Day_instInhabitedOffset___aux__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOffset___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_instInhabitedOffset___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_instInhabitedOffset___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Day_instInhabitedOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Day_instAddOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Day_instAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_instSubOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Day_instSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_instNegOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Day_instNegOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instNegOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instLEOffset: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Day_instLTOffset: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Day_instToStringOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Day_instToStringOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instToStringOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_instOrdOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Day_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Day_instOrdOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Day_instOrdOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_instReprOfYear___closed__0_value:
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
    m_fun: l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Day_Ordinal_instReprOfYear___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_instReprOfYear___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14249328086033210933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14_value:
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
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_1:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_2:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__14_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Day_Ordinal_ofNat___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Ordinal_ofFin___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Ordinal_ofFin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Offset_toNanoseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Offset_toNanoseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Offset_toMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Offset_toMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Offset_toSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Offset_toSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Offset_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Offset_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Day_Offset_toHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Offset_toHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_597_ = lean_nat_to_int(v___x_596_);
    return v___x_597_;
}
pub unsafe fn l_Std_Time_Day_instReprOrdinal___aux__1(
    mut v_n_598_: *mut crate::leanh::LeanObject,
    mut v_a_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: u8 = 0;
    v___x_600_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0,
    );
    v___x_601_ = lean_int_dec_lt(v_n_598_, v___x_600_);
    if v___x_601_ == 0 {
        let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_602_ = l_Int_repr(v_n_598_);
        v___x_603_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_603_, 0, v___x_602_);
        return v___x_603_;
    } else {
        let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_604_ = l_Int_repr(v_n_598_);
        v___x_605_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_605_, 0, v___x_604_);
        v___x_606_ = l_Repr_addAppParen(v___x_605_, v_a_599_);
        return v___x_606_;
    }
}
pub unsafe fn l_Std_Time_Day_instReprOrdinal___aux__1___boxed(
    mut v_n_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l_Std_Time_Day_instReprOrdinal___aux__1(v_n_607_, v_a_608_);
    crate::leanh::lean_dec(v_a_608_);
    crate::leanh::lean_dec(v_n_607_);
    return v_res_609_;
}
pub unsafe fn l_Std_Time_Day_instReprOrdinal___lam__0(
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: u8 = 0;
    v___x_612_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0,
    );
    v___x_613_ = lean_int_dec_lt(v___y_610_, v___x_612_);
    if v___x_613_ == 0 {
        let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_614_ = l_Int_repr(v___y_610_);
        v___x_615_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_615_, 0, v___x_614_);
        return v___x_615_;
    } else {
        let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_616_ = l_Int_repr(v___y_610_);
        v___x_617_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_617_, 0, v___x_616_);
        v___x_618_ = l_Repr_addAppParen(v___x_617_, v___y_611_);
        return v___x_618_;
    }
}
pub unsafe fn l_Std_Time_Day_instReprOrdinal___lam__0___boxed(
    mut v___y_619_: *mut crate::leanh::LeanObject,
    mut v___y_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Std_Time_Day_instReprOrdinal___lam__0(v___y_619_, v___y_620_);
    crate::leanh::lean_dec(v___y_620_);
    crate::leanh::lean_dec(v___y_619_);
    return v_res_621_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOrdinal___aux__1(
    mut v_a_624_: *mut crate::leanh::LeanObject,
    mut v_b_625_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_626_: u8 = 0;
    v___x_626_ = lean_int_dec_eq(v_a_624_, v_b_625_);
    return v___x_626_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_627_: *mut crate::leanh::LeanObject,
    mut v_b_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_629_: u8 = 0;
    let mut v_r_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Std_Time_Day_instDecidableEqOrdinal___aux__1(v_a_627_, v_b_628_);
    crate::leanh::lean_dec(v_b_628_);
    crate::leanh::lean_dec(v_a_627_);
    v_r_630_ = crate::leanh::lean_box((v_res_629_) as usize);
    return v_r_630_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOrdinal(
    mut v_a_631_: *mut crate::leanh::LeanObject,
    mut v_b_632_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_633_: u8 = 0;
    v___x_633_ = lean_int_dec_eq(v_a_631_, v_b_632_);
    return v___x_633_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOrdinal___boxed(
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_b_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_636_: u8 = 0;
    let mut v_r_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_636_ = l_Std_Time_Day_instDecidableEqOrdinal(v_a_634_, v_b_635_);
    crate::leanh::lean_dec(v_b_635_);
    crate::leanh::lean_dec(v_a_634_);
    v_r_637_ = crate::leanh::lean_box((v_res_636_) as usize);
    return v_r_637_;
}
pub unsafe fn _init_l_Std_Time_Day_instLEOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = crate::leanh::lean_box(0);
    return v___x_638_;
}
pub unsafe fn _init_l_Std_Time_Day_instLTOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = crate::leanh::lean_box(0);
    return v___x_639_;
}
pub unsafe fn _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_641_ = lean_nat_to_int(v___x_640_);
    return v___x_641_;
}
pub unsafe fn _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_642_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_643_ = lean_nat_to_int(v___x_642_);
    return v___x_643_;
}
pub unsafe fn _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_645_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_646_ = lean_int_add(v___x_645_, v___x_644_);
    return v___x_646_;
}
pub unsafe fn _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_648_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__2,
    );
    v___x_649_ = lean_int_sub(v___x_648_, v___x_647_);
    return v___x_649_;
}
pub unsafe fn _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_651_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__3,
    );
    v_range_652_ = lean_int_add(v___x_651_, v___x_650_);
    return v_range_652_;
}
pub unsafe fn l_Std_Time_Day_instOfNatOrdinal___aux__1(
    mut v_n_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_655_ = lean_nat_to_int(v_n_653_);
    v_range_656_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_657_ = lean_int_sub(v___x_655_, v___x_654_);
    crate::leanh::lean_dec(v___x_655_);
    v___x_658_ = lean_int_emod(v___x_657_, v_range_656_);
    crate::leanh::lean_dec(v___x_657_);
    v___x_659_ = lean_int_add(v___x_658_, v_range_656_);
    crate::leanh::lean_dec(v___x_658_);
    v___x_660_ = lean_int_emod(v___x_659_, v_range_656_);
    crate::leanh::lean_dec(v___x_659_);
    v___x_661_ = lean_int_add(v___x_660_, v___x_654_);
    crate::leanh::lean_dec(v___x_660_);
    return v___x_661_;
}
pub unsafe fn l_Std_Time_Day_instOfNatOrdinal(
    mut v_n_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_664_ = lean_nat_to_int(v_n_662_);
    v_range_665_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_666_ = lean_int_sub(v___x_664_, v___x_663_);
    crate::leanh::lean_dec(v___x_664_);
    v___x_667_ = lean_int_emod(v___x_666_, v_range_665_);
    crate::leanh::lean_dec(v___x_666_);
    v___x_668_ = lean_int_add(v___x_667_, v_range_665_);
    crate::leanh::lean_dec(v___x_667_);
    v___x_669_ = lean_int_emod(v___x_668_, v_range_665_);
    crate::leanh::lean_dec(v___x_668_);
    v___x_670_ = lean_int_add(v___x_669_, v___x_663_);
    crate::leanh::lean_dec(v___x_669_);
    return v___x_670_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOrdinal___aux__1(
    mut v_x_671_: *mut crate::leanh::LeanObject,
    mut v_y_672_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_673_: u8 = 0;
    v___x_673_ = lean_int_dec_le(v_x_671_, v_y_672_);
    return v___x_673_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_674_: *mut crate::leanh::LeanObject,
    mut v_y_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_676_: u8 = 0;
    let mut v_r_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_676_ = l_Std_Time_Day_instDecidableLeOrdinal___aux__1(v_x_674_, v_y_675_);
    crate::leanh::lean_dec(v_y_675_);
    crate::leanh::lean_dec(v_x_674_);
    v_r_677_ = crate::leanh::lean_box((v_res_676_) as usize);
    return v_r_677_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOrdinal(
    mut v___y_678_: *mut crate::leanh::LeanObject,
    mut v___y_679_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_680_: u8 = 0;
    v___x_680_ = lean_int_dec_le(v___y_678_, v___y_679_);
    return v___x_680_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOrdinal___boxed(
    mut v___y_681_: *mut crate::leanh::LeanObject,
    mut v___y_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: u8 = 0;
    let mut v_r_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Std_Time_Day_instDecidableLeOrdinal(v___y_681_, v___y_682_);
    crate::leanh::lean_dec(v___y_682_);
    crate::leanh::lean_dec(v___y_681_);
    v_r_684_ = crate::leanh::lean_box((v_res_683_) as usize);
    return v_r_684_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOrdinal___aux__1(
    mut v_x_685_: *mut crate::leanh::LeanObject,
    mut v_y_686_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_687_: u8 = 0;
    v___x_687_ = lean_int_dec_lt(v_x_685_, v_y_686_);
    return v___x_687_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_688_: *mut crate::leanh::LeanObject,
    mut v_y_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_690_: u8 = 0;
    let mut v_r_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_690_ = l_Std_Time_Day_instDecidableLtOrdinal___aux__1(v_x_688_, v_y_689_);
    crate::leanh::lean_dec(v_y_689_);
    crate::leanh::lean_dec(v_x_688_);
    v_r_691_ = crate::leanh::lean_box((v_res_690_) as usize);
    return v_r_691_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOrdinal(
    mut v___y_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_694_: u8 = 0;
    v___x_694_ = lean_int_dec_lt(v___y_692_, v___y_693_);
    return v___x_694_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOrdinal___boxed(
    mut v___y_695_: *mut crate::leanh::LeanObject,
    mut v___y_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_697_: u8 = 0;
    let mut v_r_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Std_Time_Day_instDecidableLtOrdinal(v___y_695_, v___y_696_);
    crate::leanh::lean_dec(v___y_696_);
    crate::leanh::lean_dec(v___y_695_);
    v_r_698_ = crate::leanh::lean_box((v_res_697_) as usize);
    return v_r_698_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_700_ = lean_int_sub(v___x_699_, v___x_699_);
    return v___x_700_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_range_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_701_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Day_instInhabitedOrdinal___closed__0,
    );
    v___x_703_ = lean_int_emod(v___x_702_, v_range_701_);
    return v___x_703_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_range_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_704_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_705_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Day_instInhabitedOrdinal___closed__1,
    );
    v___x_706_ = lean_int_add(v___x_705_, v_range_704_);
    return v___x_706_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_range_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_707_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_708_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Day_instInhabitedOrdinal___closed__2,
    );
    v___x_709_ = lean_int_emod(v___x_708_, v_range_707_);
    return v___x_709_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_711_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Day_instInhabitedOrdinal___closed__3,
    );
    v___x_712_ = lean_int_add(v___x_711_, v___x_710_);
    return v___x_712_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Day_instInhabitedOrdinal___closed__4,
    );
    return v___x_713_;
}
pub unsafe fn l_Std_Time_Day_instOrdOrdinal___aux__1(
    mut v_x_714_: *mut crate::leanh::LeanObject,
    mut v_y_715_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_716_: u8 = 0;
    v___x_716_ = lean_int_dec_lt(v_x_714_, v_y_715_);
    if v___x_716_ == 0 {
        let mut v___x_717_: u8 = 0;
        v___x_717_ = lean_int_dec_eq(v_x_714_, v_y_715_);
        if v___x_717_ == 0 {
            let mut v___x_718_: u8 = 0;
            v___x_718_ = 2;
            return v___x_718_;
        } else {
            let mut v___x_719_: u8 = 0;
            v___x_719_ = 1;
            return v___x_719_;
        }
    } else {
        let mut v___x_720_: u8 = 0;
        v___x_720_ = 0;
        return v___x_720_;
    }
}
pub unsafe fn l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_y_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Std_Time_Day_instOrdOrdinal___aux__1(v_x_721_, v_y_722_);
    crate::leanh::lean_dec(v_y_722_);
    crate::leanh::lean_dec(v_x_721_);
    v_r_724_ = crate::leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l_Std_Time_Day_instReprOffset___aux__1(
    mut v_x_727_: *mut crate::leanh::LeanObject,
    mut v_p_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    v___x_729_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0,
    );
    v___x_730_ = lean_int_dec_lt(v_x_727_, v___x_729_);
    if v___x_730_ == 0 {
        let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_731_ = l_Int_repr(v_x_727_);
        v___x_732_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_731_);
        return v___x_732_;
    } else {
        let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_733_ = l_Int_repr(v_x_727_);
        v___x_734_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_734_, 0, v___x_733_);
        v___x_735_ = l_Repr_addAppParen(v___x_734_, v_p_728_);
        return v___x_735_;
    }
}
pub unsafe fn l_Std_Time_Day_instReprOffset___aux__1___boxed(
    mut v_x_736_: *mut crate::leanh::LeanObject,
    mut v_p_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_738_ = l_Std_Time_Day_instReprOffset___aux__1(v_x_736_, v_p_737_);
    crate::leanh::lean_dec(v_p_737_);
    crate::leanh::lean_dec(v_x_736_);
    return v_res_738_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOffset___aux__1(
    mut v_a_740_: *mut crate::leanh::LeanObject,
    mut v_b_741_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_742_: u8 = 0;
    v___x_742_ = lean_int_dec_eq(v_a_740_, v_b_741_);
    return v___x_742_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOffset___aux__1___boxed(
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_b_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_745_: u8 = 0;
    let mut v_r_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Std_Time_Day_instDecidableEqOffset___aux__1(v_a_743_, v_b_744_);
    crate::leanh::lean_dec(v_b_744_);
    crate::leanh::lean_dec(v_a_743_);
    v_r_746_ = crate::leanh::lean_box((v_res_745_) as usize);
    return v_r_746_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_748_ = lean_nat_to_int(v_a_747_);
    return v___x_748_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = lean_nat_to_int(v_a_749_);
    v___x_751_ = l_Rat_ofInt(v___x_750_);
    return v___x_751_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOffset(
    mut v_a_752_: *mut crate::leanh::LeanObject,
    mut v_b_753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_754_: u8 = 0;
    v___x_754_ = lean_int_dec_eq(v_a_752_, v_b_753_);
    return v___x_754_;
}
pub unsafe fn l_Std_Time_Day_instDecidableEqOffset___boxed(
    mut v_a_755_: *mut crate::leanh::LeanObject,
    mut v_b_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_757_: u8 = 0;
    let mut v_r_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Std_Time_Day_instDecidableEqOffset(v_a_755_, v_b_756_);
    crate::leanh::lean_dec(v_b_756_);
    crate::leanh::lean_dec(v_a_755_);
    v_r_758_ = crate::leanh::lean_box((v_res_757_) as usize);
    return v_r_758_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_760_ = l_Rat_instNatCast___lam__0(v___x_759_);
    return v___x_760_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_762_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_761_);
    return v___x_762_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOffset___aux__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Day_instInhabitedOffset___aux__1___closed__1,
    );
    return v___x_763_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOffset___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_765_ =
        l_Nat_cast___at___00Std_Time_Day_instDecidableEqOffset___aux__1_spec__0(v___x_764_);
    return v___x_765_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOffset___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Day_instInhabitedOffset___closed__0,
    );
    v___x_767_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_766_);
    return v___x_767_;
}
pub unsafe fn _init_l_Std_Time_Day_instInhabitedOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Day_instInhabitedOffset___closed__1,
    );
    return v___x_768_;
}
pub unsafe fn l_Std_Time_Day_instAddOffset___aux__1(
    mut v_u1_769_: *mut crate::leanh::LeanObject,
    mut v_u2_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = lean_int_add(v_u1_769_, v_u2_770_);
    return v___x_771_;
}
pub unsafe fn l_Std_Time_Day_instAddOffset___aux__1___boxed(
    mut v_u1_772_: *mut crate::leanh::LeanObject,
    mut v_u2_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l_Std_Time_Day_instAddOffset___aux__1(v_u1_772_, v_u2_773_);
    crate::leanh::lean_dec(v_u2_773_);
    crate::leanh::lean_dec(v_u1_772_);
    return v_res_774_;
}
pub unsafe fn l_Std_Time_Day_instSubOffset___aux__1(
    mut v_u1_777_: *mut crate::leanh::LeanObject,
    mut v_u2_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = lean_int_sub(v_u1_777_, v_u2_778_);
    return v___x_779_;
}
pub unsafe fn l_Std_Time_Day_instSubOffset___aux__1___boxed(
    mut v_u1_780_: *mut crate::leanh::LeanObject,
    mut v_u2_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Std_Time_Day_instSubOffset___aux__1(v_u1_780_, v_u2_781_);
    crate::leanh::lean_dec(v_u2_781_);
    crate::leanh::lean_dec(v_u1_780_);
    return v_res_782_;
}
pub unsafe fn l_Std_Time_Day_instNegOffset___aux__1(
    mut v_x_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = lean_int_neg(v_x_785_);
    return v___x_786_;
}
pub unsafe fn l_Std_Time_Day_instNegOffset___aux__1___boxed(
    mut v_x_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l_Std_Time_Day_instNegOffset___aux__1(v_x_787_);
    crate::leanh::lean_dec(v_x_787_);
    return v_res_788_;
}
pub unsafe fn _init_l_Std_Time_Day_instLEOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_791_ = crate::leanh::lean_box(0);
    return v___x_791_;
}
pub unsafe fn _init_l_Std_Time_Day_instLTOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = crate::leanh::lean_box(0);
    return v___x_792_;
}
pub unsafe fn l_Std_Time_Day_instToStringOffset___aux__1(
    mut v_n_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = l_Int_repr(v_n_793_);
    return v___x_794_;
}
pub unsafe fn l_Std_Time_Day_instToStringOffset___aux__1___boxed(
    mut v_n_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l_Std_Time_Day_instToStringOffset___aux__1(v_n_795_);
    crate::leanh::lean_dec(v_n_795_);
    return v_res_796_;
}
pub unsafe fn l_Std_Time_Day_instOfNatOffset(
    mut v_n_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = lean_nat_to_int(v_n_799_);
    return v___x_800_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOffset___aux__1(
    mut v_x_801_: *mut crate::leanh::LeanObject,
    mut v_y_802_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_803_: u8 = 0;
    v___x_803_ = lean_int_dec_le(v_x_801_, v_y_802_);
    return v___x_803_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOffset___aux__1___boxed(
    mut v_x_804_: *mut crate::leanh::LeanObject,
    mut v_y_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Std_Time_Day_instDecidableLeOffset___aux__1(v_x_804_, v_y_805_);
    crate::leanh::lean_dec(v_y_805_);
    crate::leanh::lean_dec(v_x_804_);
    v_r_807_ = crate::leanh::lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOffset(
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_810_: u8 = 0;
    v___x_810_ = lean_int_dec_le(v___y_808_, v___y_809_);
    return v___x_810_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLeOffset___boxed(
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_813_: u8 = 0;
    let mut v_r_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Std_Time_Day_instDecidableLeOffset(v___y_811_, v___y_812_);
    crate::leanh::lean_dec(v___y_812_);
    crate::leanh::lean_dec(v___y_811_);
    v_r_814_ = crate::leanh::lean_box((v_res_813_) as usize);
    return v_r_814_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOffset___aux__1(
    mut v_x_815_: *mut crate::leanh::LeanObject,
    mut v_y_816_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_817_: u8 = 0;
    v___x_817_ = lean_int_dec_lt(v_x_815_, v_y_816_);
    return v___x_817_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOffset___aux__1___boxed(
    mut v_x_818_: *mut crate::leanh::LeanObject,
    mut v_y_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_820_: u8 = 0;
    let mut v_r_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Std_Time_Day_instDecidableLtOffset___aux__1(v_x_818_, v_y_819_);
    crate::leanh::lean_dec(v_y_819_);
    crate::leanh::lean_dec(v_x_818_);
    v_r_821_ = crate::leanh::lean_box((v_res_820_) as usize);
    return v_r_821_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOffset(
    mut v___y_822_: *mut crate::leanh::LeanObject,
    mut v___y_823_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_824_: u8 = 0;
    v___x_824_ = lean_int_dec_lt(v___y_822_, v___y_823_);
    return v___x_824_;
}
pub unsafe fn l_Std_Time_Day_instDecidableLtOffset___boxed(
    mut v___y_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_827_: u8 = 0;
    let mut v_r_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Std_Time_Day_instDecidableLtOffset(v___y_825_, v___y_826_);
    crate::leanh::lean_dec(v___y_826_);
    crate::leanh::lean_dec(v___y_825_);
    v_r_828_ = crate::leanh::lean_box((v_res_827_) as usize);
    return v_r_828_;
}
pub unsafe fn l_Std_Time_Day_instOrdOffset___aux__1(
    mut v_x_829_: *mut crate::leanh::LeanObject,
    mut v_y_830_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_831_: u8 = 0;
    v___x_831_ = lean_int_dec_lt(v_x_829_, v_y_830_);
    if v___x_831_ == 0 {
        let mut v___x_832_: u8 = 0;
        v___x_832_ = lean_int_dec_eq(v_x_829_, v_y_830_);
        if v___x_832_ == 0 {
            let mut v___x_833_: u8 = 0;
            v___x_833_ = 2;
            return v___x_833_;
        } else {
            let mut v___x_834_: u8 = 0;
            v___x_834_ = 1;
            return v___x_834_;
        }
    } else {
        let mut v___x_835_: u8 = 0;
        v___x_835_ = 0;
        return v___x_835_;
    }
}
pub unsafe fn l_Std_Time_Day_instOrdOffset___aux__1___boxed(
    mut v_x_836_: *mut crate::leanh::LeanObject,
    mut v_y_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: u8 = 0;
    let mut v_r_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Std_Time_Day_instOrdOffset___aux__1(v_x_836_, v_y_837_);
    crate::leanh::lean_dec(v_y_837_);
    crate::leanh::lean_dec(v_x_836_);
    v_r_839_ = crate::leanh::lean_box((v_res_838_) as usize);
    return v_r_839_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofInt___redArg(
    mut v_data_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_842_);
    return v_data_842_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofInt___redArg___boxed(
    mut v_data_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Std_Time_Day_Ordinal_ofInt___redArg(v_data_843_);
    crate::leanh::lean_dec(v_data_843_);
    return v_res_844_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofInt(
    mut v_data_845_: *mut crate::leanh::LeanObject,
    mut v_h_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_845_);
    return v_data_845_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofInt___boxed(
    mut v_data_847_: *mut crate::leanh::LeanObject,
    mut v_h_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Std_Time_Day_Ordinal_ofInt(v_data_847_, v_h_848_);
    crate::leanh::lean_dec(v_data_847_);
    return v_res_849_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(
    mut v_r_850_: *mut crate::leanh::LeanObject,
    mut v_p_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    v___x_852_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instReprOrdinal___aux__1___closed__0,
    );
    v___x_853_ = lean_int_dec_lt(v_r_850_, v___x_852_);
    if v___x_853_ == 0 {
        let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_854_ = l_Int_repr(v_r_850_);
        v___x_855_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_855_, 0, v___x_854_);
        return v___x_855_;
    } else {
        let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_856_ = l_Int_repr(v_r_850_);
        v___x_857_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_856_);
        v___x_858_ = l_Repr_addAppParen(v___x_857_, v_p_851_);
        return v___x_858_;
    }
}
pub unsafe fn l_Std_Time_Day_Ordinal_instReprOfYear___lam__0___boxed(
    mut v_r_859_: *mut crate::leanh::LeanObject,
    mut v_p_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Std_Time_Day_Ordinal_instReprOfYear___lam__0(v_r_859_, v_p_860_);
    crate::leanh::lean_dec(v_p_860_);
    crate::leanh::lean_dec(v_r_859_);
    return v_res_861_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instReprOfYear(
    mut v_leap_863_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_864_ = l_Std_Time_Day_Ordinal_instReprOfYear___closed__0;
    return v___f_864_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instReprOfYear___boxed(
    mut v_leap_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_866_: u8 = 0;
    let mut v_res_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_866_ = (crate::leanh::lean_unbox(v_leap_865_) as u8);
    v_res_867_ = l_Std_Time_Day_Ordinal_instReprOfYear(v_leap_boxed_866_);
    return v_res_867_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instToStringOfYear(
    mut v_leap_868_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_869_ = l_Std_Time_Day_instToStringOffset___closed__0;
    return v___f_869_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instToStringOfYear___boxed(
    mut v_leap_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_871_: u8 = 0;
    let mut v_res_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_871_ = (crate::leanh::lean_unbox(v_leap_870_) as u8);
    v_res_872_ = l_Std_Time_Day_Ordinal_instToStringOfYear(v_leap_boxed_871_);
    return v_res_872_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(
    mut v_a_873_: *mut crate::leanh::LeanObject,
    mut v_b_874_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_875_: u8 = 0;
    v___x_875_ = lean_int_dec_eq(v_a_873_, v_b_874_);
    return v___x_875_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg___boxed(
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_b_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_878_: u8 = 0;
    let mut v_r_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___redArg(v_a_876_, v_b_877_);
    crate::leanh::lean_dec(v_b_877_);
    crate::leanh::lean_dec(v_a_876_);
    v_r_879_ = crate::leanh::lean_box((v_res_878_) as usize);
    return v_r_879_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(
    mut v_leap_880_: u8,
    mut v_a_881_: *mut crate::leanh::LeanObject,
    mut v_b_882_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_883_: u8 = 0;
    v___x_883_ = lean_int_dec_eq(v_a_881_, v_b_882_);
    return v___x_883_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1___boxed(
    mut v_leap_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_b_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_887_: u8 = 0;
    let mut v_res_888_: u8 = 0;
    let mut v_r_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_887_ = (crate::leanh::lean_unbox(v_leap_884_) as u8);
    v_res_888_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___aux__1(
        v_leap_boxed_887_,
        v_a_885_,
        v_b_886_,
    );
    crate::leanh::lean_dec(v_b_886_);
    crate::leanh::lean_dec(v_a_885_);
    v_r_889_ = crate::leanh::lean_box((v_res_888_) as usize);
    return v_r_889_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(
    mut v_a_890_: *mut crate::leanh::LeanObject,
    mut v_b_891_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_892_: u8 = 0;
    v___x_892_ = lean_int_dec_eq(v_a_890_, v_b_891_);
    return v___x_892_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg___boxed(
    mut v_a_893_: *mut crate::leanh::LeanObject,
    mut v_b_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_895_: u8 = 0;
    let mut v_r_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Std_Time_Day_Ordinal_instDecidableEqOfYear___redArg(v_a_893_, v_b_894_);
    crate::leanh::lean_dec(v_b_894_);
    crate::leanh::lean_dec(v_a_893_);
    v_r_896_ = crate::leanh::lean_box((v_res_895_) as usize);
    return v_r_896_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear(
    mut v_leap_897_: u8,
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_b_899_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_900_: u8 = 0;
    v___x_900_ = lean_int_dec_eq(v_a_898_, v_b_899_);
    return v___x_900_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instDecidableEqOfYear___boxed(
    mut v_leap_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_b_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_904_: u8 = 0;
    let mut v_res_905_: u8 = 0;
    let mut v_r_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_904_ = (crate::leanh::lean_unbox(v_leap_901_) as u8);
    v_res_905_ =
        l_Std_Time_Day_Ordinal_instDecidableEqOfYear(v_leap_boxed_904_, v_a_902_, v_b_903_);
    crate::leanh::lean_dec(v_b_903_);
    crate::leanh::lean_dec(v_a_902_);
    v_r_906_ = crate::leanh::lean_box((v_res_905_) as usize);
    return v_r_906_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(
    mut v_x_907_: *mut crate::leanh::LeanObject,
    mut v_y_908_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_909_: u8 = 0;
    v___x_909_ = lean_int_dec_lt(v_x_907_, v_y_908_);
    if v___x_909_ == 0 {
        let mut v___x_910_: u8 = 0;
        v___x_910_ = lean_int_dec_eq(v_x_907_, v_y_908_);
        if v___x_910_ == 0 {
            let mut v___x_911_: u8 = 0;
            v___x_911_ = 2;
            return v___x_911_;
        } else {
            let mut v___x_912_: u8 = 0;
            v___x_912_ = 1;
            return v___x_912_;
        }
    } else {
        let mut v___x_913_: u8 = 0;
        v___x_913_ = 0;
        return v___x_913_;
    }
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg___boxed(
    mut v_x_914_: *mut crate::leanh::LeanObject,
    mut v_y_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_916_: u8 = 0;
    let mut v_r_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ = l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___redArg(v_x_914_, v_y_915_);
    crate::leanh::lean_dec(v_y_915_);
    crate::leanh::lean_dec(v_x_914_);
    v_r_917_ = crate::leanh::lean_box((v_res_916_) as usize);
    return v_r_917_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(
    mut v_leap_918_: u8,
    mut v_x_919_: *mut crate::leanh::LeanObject,
    mut v_y_920_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_921_: u8 = 0;
    v___x_921_ = lean_int_dec_lt(v_x_919_, v_y_920_);
    if v___x_921_ == 0 {
        let mut v___x_922_: u8 = 0;
        v___x_922_ = lean_int_dec_eq(v_x_919_, v_y_920_);
        if v___x_922_ == 0 {
            let mut v___x_923_: u8 = 0;
            v___x_923_ = 2;
            return v___x_923_;
        } else {
            let mut v___x_924_: u8 = 0;
            v___x_924_ = 1;
            return v___x_924_;
        }
    } else {
        let mut v___x_925_: u8 = 0;
        v___x_925_ = 0;
        return v___x_925_;
    }
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed(
    mut v_leap_926_: *mut crate::leanh::LeanObject,
    mut v_x_927_: *mut crate::leanh::LeanObject,
    mut v_y_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_929_: u8 = 0;
    let mut v_res_930_: u8 = 0;
    let mut v_r_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_929_ = (crate::leanh::lean_unbox(v_leap_926_) as u8);
    v_res_930_ =
        l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1(v_leap_boxed_929_, v_x_927_, v_y_928_);
    crate::leanh::lean_dec(v_y_928_);
    crate::leanh::lean_dec(v_x_927_);
    v_r_931_ = crate::leanh::lean_box((v_res_930_) as usize);
    return v_r_931_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOrdOfYear(
    mut v_leap_932_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = crate::leanh::lean_box((v_leap_932_) as usize);
    v___x_934_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_Day_Ordinal_instOrdOfYear___aux__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_934_, 0, v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOrdOfYear___boxed(
    mut v_leap_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_936_: u8 = 0;
    let mut v_res_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_936_ = (crate::leanh::lean_unbox(v_leap_935_) as u8);
    v_res_937_ = l_Std_Time_Day_Ordinal_instOrdOfYear(v_leap_boxed_936_);
    return v_res_937_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__10;
    v___x_965_ = l_Lean_mkAtom(v___x_964_);
    return v___x_965_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_966_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__12,
    );
    v___x_967_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5;
    v___x_968_ = lean_array_push(v___x_967_, v___x_966_);
    return v___x_968_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__16;
    v___x_980_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5;
    v___x_981_ = lean_array_push(v___x_980_, v___x_979_);
    return v___x_981_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__17,
    );
    v___x_983_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__15;
    v___x_984_ = crate::leanh::lean_box(2);
    v___x_985_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_985_, 0, v___x_984_);
    crate::leanh::lean_ctor_set(v___x_985_, 1, v___x_983_);
    crate::leanh::lean_ctor_set(v___x_985_, 2, v___x_982_);
    return v___x_985_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__18,
    );
    v___x_987_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__13,
    );
    v___x_988_ = lean_array_push(v___x_987_, v___x_986_);
    return v___x_988_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__19,
    );
    v___x_990_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__11;
    v___x_991_ = crate::leanh::lean_box(2);
    v___x_992_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
    crate::leanh::lean_ctor_set(v___x_992_, 1, v___x_990_);
    crate::leanh::lean_ctor_set(v___x_992_, 2, v___x_989_);
    return v___x_992_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__20,
    );
    v___x_994_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5;
    v___x_995_ = lean_array_push(v___x_994_, v___x_993_);
    return v___x_995_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_996_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__21,
    );
    v___x_997_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__9;
    v___x_998_ = crate::leanh::lean_box(2);
    v___x_999_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_999_, 0, v___x_998_);
    crate::leanh::lean_ctor_set(v___x_999_, 1, v___x_997_);
    crate::leanh::lean_ctor_set(v___x_999_, 2, v___x_996_);
    return v___x_999_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__22,
    );
    v___x_1001_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5;
    v___x_1002_ = lean_array_push(v___x_1001_, v___x_1000_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__23,
    );
    v___x_1004_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__7;
    v___x_1005_ = crate::leanh::lean_box(2);
    v___x_1006_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1006_, 0, v___x_1005_);
    crate::leanh::lean_ctor_set(v___x_1006_, 1, v___x_1004_);
    crate::leanh::lean_ctor_set(v___x_1006_, 2, v___x_1003_);
    return v___x_1006_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__24,
    );
    v___x_1008_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__5;
    v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__25,
    );
    v___x_1011_ = l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__4;
    v___x_1012_ = crate::leanh::lean_box(2);
    v___x_1013_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1012_);
    crate::leanh::lean_ctor_set(v___x_1013_, 1, v___x_1011_);
    crate::leanh::lean_ctor_set(v___x_1013_, 2, v___x_1010_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26,
    );
    return v___x_1014_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_ofNat___redArg(
    mut v_data_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = lean_nat_to_int(v_data_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_ofNat(
    mut v_leap_1017_: u8,
    mut v_data_1018_: *mut crate::leanh::LeanObject,
    mut v_h_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = lean_nat_to_int(v_data_1018_);
    return v___x_1020_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_ofNat___boxed(
    mut v_leap_1021_: *mut crate::leanh::LeanObject,
    mut v_data_1022_: *mut crate::leanh::LeanObject,
    mut v_h_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1024_: u8 = 0;
    let mut v_res_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1024_ = (crate::leanh::lean_unbox(v_leap_1021_) as u8);
    v_res_1025_ = l_Std_Time_Day_Ordinal_OfYear_ofNat(v_leap_boxed_1024_, v_data_1022_, v_h_1023_);
    return v_res_1025_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = crate::leanh::lean_unsigned_to_nat(365);
    v___x_1027_ = lean_nat_to_int(v___x_1026_);
    return v___x_1027_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__0,
    );
    v___x_1029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1030_ = lean_int_add(v___x_1029_, v___x_1028_);
    return v___x_1030_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1032_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__1,
    );
    v___x_1033_ = lean_int_sub(v___x_1032_, v___x_1031_);
    return v___x_1033_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1035_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__2,
    );
    v_range_1036_ = lean_int_add(v___x_1035_, v___x_1034_);
    return v_range_1036_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1(
    mut v_n_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1039_ = lean_nat_to_int(v_n_1037_);
    v_range_1040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3,
    );
    v___x_1041_ = lean_int_sub(v___x_1039_, v___x_1038_);
    crate::leanh::lean_dec(v___x_1039_);
    v___x_1042_ = lean_int_emod(v___x_1041_, v_range_1040_);
    crate::leanh::lean_dec(v___x_1041_);
    v___x_1043_ = lean_int_add(v___x_1042_, v_range_1040_);
    crate::leanh::lean_dec(v___x_1042_);
    v___x_1044_ = lean_int_emod(v___x_1043_, v_range_1040_);
    crate::leanh::lean_dec(v___x_1043_);
    v___x_1045_ = lean_int_add(v___x_1044_, v___x_1038_);
    crate::leanh::lean_dec(v___x_1044_);
    return v___x_1045_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = crate::leanh::lean_unsigned_to_nat(364);
    v___x_1047_ = lean_nat_to_int(v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__0,
    );
    v___x_1049_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1050_ = lean_int_add(v___x_1049_, v___x_1048_);
    return v___x_1050_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__1,
    );
    v___x_1053_ = lean_int_sub(v___x_1052_, v___x_1051_);
    return v___x_1053_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1055_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__2,
    );
    v_range_1056_ = lean_int_add(v___x_1055_, v___x_1054_);
    return v_range_1056_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3(
    mut v_n_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_1059_ = lean_nat_to_int(v_n_1057_);
    v_range_1060_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once),
        _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3,
    );
    v___x_1061_ = lean_int_sub(v___x_1059_, v___x_1058_);
    crate::leanh::lean_dec(v___x_1059_);
    v___x_1062_ = lean_int_emod(v___x_1061_, v_range_1060_);
    crate::leanh::lean_dec(v___x_1061_);
    v___x_1063_ = lean_int_add(v___x_1062_, v_range_1060_);
    crate::leanh::lean_dec(v___x_1062_);
    v___x_1064_ = lean_int_emod(v___x_1063_, v_range_1060_);
    crate::leanh::lean_dec(v___x_1063_);
    v___x_1065_ = lean_int_add(v___x_1064_, v___x_1058_);
    crate::leanh::lean_dec(v___x_1064_);
    return v___x_1065_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOfNatOfYear(
    mut v_leap_1066_: u8,
    mut v_n_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_leap_1066_ == 0 {
        let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_range_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1068_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
            _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
        );
        v___x_1069_ = lean_nat_to_int(v_n_1067_);
        v_range_1070_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3),
            core::ptr::addr_of_mut!(
                l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3_once
            ),
            _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__3___closed__3,
        );
        v___x_1071_ = lean_int_sub(v___x_1069_, v___x_1068_);
        crate::leanh::lean_dec(v___x_1069_);
        v___x_1072_ = lean_int_emod(v___x_1071_, v_range_1070_);
        crate::leanh::lean_dec(v___x_1071_);
        v___x_1073_ = lean_int_add(v___x_1072_, v_range_1070_);
        crate::leanh::lean_dec(v___x_1072_);
        v___x_1074_ = lean_int_emod(v___x_1073_, v_range_1070_);
        crate::leanh::lean_dec(v___x_1073_);
        v___x_1075_ = lean_int_add(v___x_1074_, v___x_1068_);
        crate::leanh::lean_dec(v___x_1074_);
        return v___x_1075_;
    } else {
        let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_range_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1076_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
            _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
        );
        v___x_1077_ = lean_nat_to_int(v_n_1067_);
        v_range_1078_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3),
            core::ptr::addr_of_mut!(
                l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3_once
            ),
            _init_l_Std_Time_Day_Ordinal_instOfNatOfYear___aux__1___closed__3,
        );
        v___x_1079_ = lean_int_sub(v___x_1077_, v___x_1076_);
        crate::leanh::lean_dec(v___x_1077_);
        v___x_1080_ = lean_int_emod(v___x_1079_, v_range_1078_);
        crate::leanh::lean_dec(v___x_1079_);
        v___x_1081_ = lean_int_add(v___x_1080_, v_range_1078_);
        crate::leanh::lean_dec(v___x_1080_);
        v___x_1082_ = lean_int_emod(v___x_1081_, v_range_1078_);
        crate::leanh::lean_dec(v___x_1081_);
        v___x_1083_ = lean_int_add(v___x_1082_, v___x_1076_);
        crate::leanh::lean_dec(v___x_1082_);
        return v___x_1083_;
    }
}
pub unsafe fn l_Std_Time_Day_Ordinal_instOfNatOfYear___boxed(
    mut v_leap_1084_: *mut crate::leanh::LeanObject,
    mut v_n_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1086_: u8 = 0;
    let mut v_res_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1086_ = (crate::leanh::lean_unbox(v_leap_1084_) as u8);
    v_res_1087_ = l_Std_Time_Day_Ordinal_instOfNatOfYear(v_leap_boxed_1086_, v_n_1085_);
    return v_res_1087_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instInhabitedOfYear(
    mut v_leap_1088_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Day_instOfNatOrdinal___aux__1___closed__0,
    );
    return v___x_1089_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_instInhabitedOfYear___boxed(
    mut v_leap_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1091_: u8 = 0;
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1091_ = (crate::leanh::lean_unbox(v_leap_1090_) as u8);
    v_res_1092_ = l_Std_Time_Day_Ordinal_instInhabitedOfYear(v_leap_boxed_1091_);
    return v_res_1092_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_ofNat___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26_once),
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3___closed__26,
    );
    return v___x_1093_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofNat___redArg(
    mut v_data_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = lean_nat_to_int(v_data_1094_);
    return v___x_1095_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofNat(
    mut v_data_1096_: *mut crate::leanh::LeanObject,
    mut v_h_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_nat_to_int(v_data_1096_);
    return v___x_1098_;
}
pub unsafe fn _init_l_Std_Time_Day_Ordinal_ofFin___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1099_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1100_ = lean_nat_to_int(v___x_1099_);
    return v___x_1100_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_ofFin(
    mut v_data_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: u8 = 0;
    v___x_1102_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1103_ = lean_nat_dec_le(v___x_1102_, v_data_1101_);
    if v___x_1103_ == 0 {
        let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_data_1101_);
        v___x_1104_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_ofFin___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Day_Ordinal_ofFin___closed__0_once),
            _init_l_Std_Time_Day_Ordinal_ofFin___closed__0,
        );
        return v___x_1104_;
    } else {
        let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1105_ = lean_nat_to_int(v_data_1101_);
        return v___x_1105_;
    }
}
pub unsafe fn l_Std_Time_Day_Ordinal_toOffset(
    mut v_ordinal_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ordinal_1106_);
    return v_ordinal_1106_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_toOffset___boxed(
    mut v_ordinal_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1108_ = l_Std_Time_Day_Ordinal_toOffset(v_ordinal_1107_);
    crate::leanh::lean_dec(v_ordinal_1107_);
    return v_res_1108_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(
    mut v_ofYear_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ofYear_1109_);
    return v_ofYear_1109_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg___boxed(
    mut v_ofYear_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_Std_Time_Day_Ordinal_OfYear_toOffset___redArg(v_ofYear_1110_);
    crate::leanh::lean_dec(v_ofYear_1110_);
    return v_res_1111_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_toOffset(
    mut v_leap_1112_: u8,
    mut v_ofYear_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ofYear_1113_);
    return v_ofYear_1113_;
}
pub unsafe fn l_Std_Time_Day_Ordinal_OfYear_toOffset___boxed(
    mut v_leap_1114_: *mut crate::leanh::LeanObject,
    mut v_ofYear_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leap_boxed_1116_: u8 = 0;
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_1116_ = (crate::leanh::lean_unbox(v_leap_1114_) as u8);
    v_res_1117_ = l_Std_Time_Day_Ordinal_OfYear_toOffset(v_leap_boxed_1116_, v_ofYear_1115_);
    crate::leanh::lean_dec(v_ofYear_1115_);
    return v_res_1117_;
}
pub unsafe fn l_Std_Time_Day_Offset_toOrdinal___redArg(
    mut v_off_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_1118_);
    return v_off_1118_;
}
pub unsafe fn l_Std_Time_Day_Offset_toOrdinal___redArg___boxed(
    mut v_off_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Std_Time_Day_Offset_toOrdinal___redArg(v_off_1119_);
    crate::leanh::lean_dec(v_off_1119_);
    return v_res_1120_;
}
pub unsafe fn l_Std_Time_Day_Offset_toOrdinal(
    mut v_off_1121_: *mut crate::leanh::LeanObject,
    mut v_h_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_1121_);
    return v_off_1121_;
}
pub unsafe fn l_Std_Time_Day_Offset_toOrdinal___boxed(
    mut v_off_1123_: *mut crate::leanh::LeanObject,
    mut v_h_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Std_Time_Day_Offset_toOrdinal(v_off_1123_, v_h_1124_);
    crate::leanh::lean_dec(v_off_1123_);
    return v_res_1125_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofNat(
    mut v_data_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = lean_nat_to_int(v_data_1126_);
    return v___x_1127_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofInt(
    mut v_data_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_1128_);
    return v_data_1128_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofInt___boxed(
    mut v_data_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Std_Time_Day_Offset_ofInt(v_data_1129_);
    crate::leanh::lean_dec(v_data_1129_);
    return v_res_1130_;
}
pub unsafe fn _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = crate::leanh::lean_cstr_to_nat(b"86400000000000\0".as_ptr().cast());
    v___x_1132_ = lean_nat_to_int(v___x_1131_);
    return v___x_1132_;
}
pub unsafe fn l_Std_Time_Day_Offset_toNanoseconds(
    mut v_days_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toNanoseconds___closed__0_once),
        _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0,
    );
    v___x_1135_ = lean_int_mul(v_days_1133_, v___x_1134_);
    return v___x_1135_;
}
pub unsafe fn l_Std_Time_Day_Offset_toNanoseconds___boxed(
    mut v_days_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Std_Time_Day_Offset_toNanoseconds(v_days_1136_);
    crate::leanh::lean_dec(v_days_1136_);
    return v_res_1137_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofNanoseconds(
    mut v_ns_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toNanoseconds___closed__0_once),
        _init_l_Std_Time_Day_Offset_toNanoseconds___closed__0,
    );
    v___x_1140_ = lean_int_ediv(v_ns_1138_, v___x_1139_);
    return v___x_1140_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofNanoseconds___boxed(
    mut v_ns_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Std_Time_Day_Offset_ofNanoseconds(v_ns_1141_);
    crate::leanh::lean_dec(v_ns_1141_);
    return v_res_1142_;
}
pub unsafe fn _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = crate::leanh::lean_unsigned_to_nat(86400000);
    v___x_1144_ = lean_nat_to_int(v___x_1143_);
    return v___x_1144_;
}
pub unsafe fn l_Std_Time_Day_Offset_toMilliseconds(
    mut v_days_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0,
    );
    v___x_1147_ = lean_int_mul(v_days_1145_, v___x_1146_);
    return v___x_1147_;
}
pub unsafe fn l_Std_Time_Day_Offset_toMilliseconds___boxed(
    mut v_days_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1149_ = l_Std_Time_Day_Offset_toMilliseconds(v_days_1148_);
    crate::leanh::lean_dec(v_days_1148_);
    return v_res_1149_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofMilliseconds(
    mut v_ms_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Day_Offset_toMilliseconds___closed__0,
    );
    v___x_1152_ = lean_int_ediv(v_ms_1150_, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofMilliseconds___boxed(
    mut v_ms_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Std_Time_Day_Offset_ofMilliseconds(v_ms_1153_);
    crate::leanh::lean_dec(v_ms_1153_);
    return v_res_1154_;
}
pub unsafe fn _init_l_Std_Time_Day_Offset_toSeconds___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_1156_ = lean_nat_to_int(v___x_1155_);
    return v___x_1156_;
}
pub unsafe fn l_Std_Time_Day_Offset_toSeconds(
    mut v_days_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Day_Offset_toSeconds___closed__0,
    );
    v___x_1159_ = lean_int_mul(v_days_1157_, v___x_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_Time_Day_Offset_toSeconds___boxed(
    mut v_days_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1161_ = l_Std_Time_Day_Offset_toSeconds(v_days_1160_);
    crate::leanh::lean_dec(v_days_1160_);
    return v_res_1161_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofSeconds(
    mut v_secs_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Day_Offset_toSeconds___closed__0,
    );
    v___x_1164_ = lean_int_ediv(v_secs_1162_, v___x_1163_);
    return v___x_1164_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofSeconds___boxed(
    mut v_secs_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Std_Time_Day_Offset_ofSeconds(v_secs_1165_);
    crate::leanh::lean_dec(v_secs_1165_);
    return v_res_1166_;
}
pub unsafe fn _init_l_Std_Time_Day_Offset_toMinutes___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ = crate::leanh::lean_unsigned_to_nat(1440);
    v___x_1168_ = lean_nat_to_int(v___x_1167_);
    return v___x_1168_;
}
pub unsafe fn l_Std_Time_Day_Offset_toMinutes(
    mut v_days_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Day_Offset_toMinutes___closed__0,
    );
    v___x_1171_ = lean_int_mul(v_days_1169_, v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Std_Time_Day_Offset_toMinutes___boxed(
    mut v_days_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l_Std_Time_Day_Offset_toMinutes(v_days_1172_);
    crate::leanh::lean_dec(v_days_1172_);
    return v_res_1173_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofMinutes(
    mut v_minutes_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Day_Offset_toMinutes___closed__0,
    );
    v___x_1176_ = lean_int_ediv(v_minutes_1174_, v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofMinutes___boxed(
    mut v_minutes_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Std_Time_Day_Offset_ofMinutes(v_minutes_1177_);
    crate::leanh::lean_dec(v_minutes_1177_);
    return v_res_1178_;
}
pub unsafe fn _init_l_Std_Time_Day_Offset_toHours___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_1180_ = lean_nat_to_int(v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Std_Time_Day_Offset_toHours(
    mut v_days_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Day_Offset_toHours___closed__0,
    );
    v___x_1183_ = lean_int_mul(v_days_1181_, v___x_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Std_Time_Day_Offset_toHours___boxed(
    mut v_days_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1185_ = l_Std_Time_Day_Offset_toHours(v_days_1184_);
    crate::leanh::lean_dec(v_days_1184_);
    return v_res_1185_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofHours(
    mut v_hours_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Day_Offset_toHours___closed__0,
    );
    v___x_1188_ = lean_int_ediv(v_hours_1186_, v___x_1187_);
    return v___x_1188_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofHours___boxed(
    mut v_hours_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ = l_Std_Time_Day_Offset_ofHours(v_hours_1189_);
    crate::leanh::lean_dec(v_hours_1189_);
    return v_res_1190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Day(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_Day_instLEOrdinal = _init_l_Std_Time_Day_instLEOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instLEOrdinal);
    l_Std_Time_Day_instLTOrdinal = _init_l_Std_Time_Day_instLTOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instLTOrdinal);
    l_Std_Time_Day_instInhabitedOrdinal = _init_l_Std_Time_Day_instInhabitedOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instInhabitedOrdinal);
    l_Std_Time_Day_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Day_instInhabitedOffset___aux__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instInhabitedOffset___aux__1);
    l_Std_Time_Day_instInhabitedOffset = _init_l_Std_Time_Day_instInhabitedOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instInhabitedOffset);
    l_Std_Time_Day_instLEOffset = _init_l_Std_Time_Day_instLEOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instLEOffset);
    l_Std_Time_Day_instLTOffset = _init_l_Std_Time_Day_instLTOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_instLTOffset);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Day(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3 =
        _init_l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_Ordinal_OfYear_ofNat___auto__3);
    l_Std_Time_Day_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Day_Ordinal_ofNat___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Day_Ordinal_ofNat___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Unit_Day(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Day(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Day(builtin);
}
