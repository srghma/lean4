// Lean compiler output
// Module: Std.Time.Date.Unit.Week
// Imports: Std.Time.Date.Unit.Day
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_instNatCast___lam__0, l_Rat_mul, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Std::Time::Date::Unit::Day::{
    initialize_Std_Time_Date_Unit_Day, runtime_initialize_Std_Time_Date_Unit_Day,
};
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_cstr_to_nat, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instReprOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_instReprOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instReprOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instReprOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instLEOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Week_instLTOrdinal: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOrdinal___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_instInhabitedOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Week_instOrdOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instOrdOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instOrdOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instReprOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_instInhabitedOffset___aux__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_instInhabitedOffset___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_instInhabitedOffset___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Week_instInhabitedOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Week_instAddOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Week_instSubOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Week_instNegOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instNegOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instNegOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instNegOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instNegOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instLEOffset: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Week_instLTOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Week_instToStringOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instToStringOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instToStringOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instToStringOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instToStringOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Week_instOrdOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_instOrdOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_instOrdOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instOrdOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Week_Ordinal_instReprOfMonth: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_instReprOrdinal___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_Ordinal_instInhabitedOfMonth: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_Week_Ordinal_instOrdOfMonth: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_instOrdOfMonth___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value: LeanStringObject<7> =
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
        m_data: [100, 101, 99, 105, 100, 101, 0],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10_value)
                as *mut LeanObject,
            14249328086033210933 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value)
        as *mut LeanObject;
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__14_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16_value)
        as *mut LeanObject;
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Week_Ordinal_ofNat___auto__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Ordinal_ofFin___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Ordinal_ofFin___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toMilliseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Offset_toMilliseconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toNanoseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Offset_toNanoseconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toSeconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Offset_toSeconds___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Offset_toMinutes___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Offset_toHours___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Week_Offset_toDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Week_Offset_toDays___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = lean_unsigned_to_nat(0);
    v___x_517_ = lean_nat_to_int(v___x_516_);
    return v___x_517_;
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___aux__1(
    mut v_n_518_: *mut LeanObject,
    mut v_a_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: u8 = 0;
    v___x_520_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_521_ = lean_int_dec_lt(v_n_518_, v___x_520_);
    if v___x_521_ == 0 {
        let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
        v___x_522_ = l_Int_repr(v_n_518_);
        v___x_523_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_523_, 0, v___x_522_);
        return v___x_523_;
    } else {
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        v___x_524_ = l_Int_repr(v_n_518_);
        v___x_525_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_525_, 0, v___x_524_);
        v___x_526_ = l_Repr_addAppParen(v___x_525_, v_a_519_);
        return v___x_526_;
    }
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___aux__1___boxed(
    mut v_n_527_: *mut LeanObject,
    mut v_a_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_529_: *mut LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Std_Time_Week_instReprOrdinal___aux__1(v_n_527_, v_a_528_);
    lean_dec(v_a_528_);
    lean_dec(v_n_527_);
    return v_res_529_;
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___lam__0(
    mut v___y_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    v___x_532_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_533_ = lean_int_dec_lt(v___y_530_, v___x_532_);
    if v___x_533_ == 0 {
        let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
        v___x_534_ = l_Int_repr(v___y_530_);
        v___x_535_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_535_, 0, v___x_534_);
        return v___x_535_;
    } else {
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
        v___x_536_ = l_Int_repr(v___y_530_);
        v___x_537_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_537_, 0, v___x_536_);
        v___x_538_ = l_Repr_addAppParen(v___x_537_, v___y_531_);
        return v___x_538_;
    }
}
pub unsafe fn l_Std_Time_Week_instReprOrdinal___lam__0___boxed(
    mut v___y_539_: *mut LeanObject,
    mut v___y_540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_541_: *mut LeanObject = core::ptr::null_mut();
    v_res_541_ = l_Std_Time_Week_instReprOrdinal___lam__0(v___y_539_, v___y_540_);
    lean_dec(v___y_540_);
    lean_dec(v___y_539_);
    return v_res_541_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal___aux__1(
    mut v_a_544_: *mut LeanObject,
    mut v_b_545_: *mut LeanObject,
) -> u8 {
    let mut v___x_546_: u8 = 0;
    v___x_546_ = lean_int_dec_eq(v_a_544_, v_b_545_);
    return v___x_546_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_547_: *mut LeanObject,
    mut v_b_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_549_: u8 = 0;
    let mut v_r_550_: *mut LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Std_Time_Week_instDecidableEqOrdinal___aux__1(v_a_547_, v_b_548_);
    lean_dec(v_b_548_);
    lean_dec(v_a_547_);
    v_r_550_ = lean_box((v_res_549_) as usize);
    return v_r_550_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal(
    mut v_a_551_: *mut LeanObject,
    mut v_b_552_: *mut LeanObject,
) -> u8 {
    let mut v___x_553_: u8 = 0;
    v___x_553_ = lean_int_dec_eq(v_a_551_, v_b_552_);
    return v___x_553_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOrdinal___boxed(
    mut v_a_554_: *mut LeanObject,
    mut v_b_555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_556_: u8 = 0;
    let mut v_r_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_556_ = l_Std_Time_Week_instDecidableEqOrdinal(v_a_554_, v_b_555_);
    lean_dec(v_b_555_);
    lean_dec(v_a_554_);
    v_r_557_ = lean_box((v_res_556_) as usize);
    return v_r_557_;
}
pub unsafe fn _init_l_Std_Time_Week_instLEOrdinal() -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = lean_box(0);
    return v___x_558_;
}
pub unsafe fn _init_l_Std_Time_Week_instLTOrdinal() -> *mut LeanObject {
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    v___x_559_ = lean_box(0);
    return v___x_559_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    v___x_560_ = lean_unsigned_to_nat(1);
    v___x_561_ = lean_nat_to_int(v___x_560_);
    return v___x_561_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1() -> *mut LeanObject {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v___x_562_ = lean_unsigned_to_nat(52);
    v___x_563_ = lean_nat_to_int(v___x_562_);
    return v___x_563_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2() -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    v___x_564_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_565_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_566_ = lean_int_add(v___x_565_, v___x_564_);
    return v___x_566_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3() -> *mut LeanObject {
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    v___x_567_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_568_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__2,
    );
    v___x_569_ = lean_int_sub(v___x_568_, v___x_567_);
    return v___x_569_;
}
pub unsafe fn _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4() -> *mut LeanObject {
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_572_: *mut LeanObject = core::ptr::null_mut();
    v___x_570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_571_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__3,
    );
    v_range_572_ = lean_int_add(v___x_571_, v___x_570_);
    return v_range_572_;
}
pub unsafe fn l_Std_Time_Week_instOfNatOrdinal___aux__1(
    mut v_n_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    v___x_574_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_575_ = lean_nat_to_int(v_n_573_);
    v_range_576_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_577_ = lean_int_sub(v___x_575_, v___x_574_);
    lean_dec(v___x_575_);
    v___x_578_ = lean_int_emod(v___x_577_, v_range_576_);
    lean_dec(v___x_577_);
    v___x_579_ = lean_int_add(v___x_578_, v_range_576_);
    lean_dec(v___x_578_);
    v___x_580_ = lean_int_emod(v___x_579_, v_range_576_);
    lean_dec(v___x_579_);
    v___x_581_ = lean_int_add(v___x_580_, v___x_574_);
    lean_dec(v___x_580_);
    return v___x_581_;
}
pub unsafe fn l_Std_Time_Week_instOfNatOrdinal(mut v_n_582_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    v___x_583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_584_ = lean_nat_to_int(v_n_582_);
    v_range_585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_586_ = lean_int_sub(v___x_584_, v___x_583_);
    lean_dec(v___x_584_);
    v___x_587_ = lean_int_emod(v___x_586_, v_range_585_);
    lean_dec(v___x_586_);
    v___x_588_ = lean_int_add(v___x_587_, v_range_585_);
    lean_dec(v___x_587_);
    v___x_589_ = lean_int_emod(v___x_588_, v_range_585_);
    lean_dec(v___x_588_);
    v___x_590_ = lean_int_add(v___x_589_, v___x_583_);
    lean_dec(v___x_589_);
    return v___x_590_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal___aux__1(
    mut v_x_591_: *mut LeanObject,
    mut v_y_592_: *mut LeanObject,
) -> u8 {
    let mut v___x_593_: u8 = 0;
    v___x_593_ = lean_int_dec_le(v_x_591_, v_y_592_);
    return v___x_593_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_594_: *mut LeanObject,
    mut v_y_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_596_: u8 = 0;
    let mut v_r_597_: *mut LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Std_Time_Week_instDecidableLeOrdinal___aux__1(v_x_594_, v_y_595_);
    lean_dec(v_y_595_);
    lean_dec(v_x_594_);
    v_r_597_ = lean_box((v_res_596_) as usize);
    return v_r_597_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal(
    mut v___y_598_: *mut LeanObject,
    mut v___y_599_: *mut LeanObject,
) -> u8 {
    let mut v___x_600_: u8 = 0;
    v___x_600_ = lean_int_dec_le(v___y_598_, v___y_599_);
    return v___x_600_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOrdinal___boxed(
    mut v___y_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_603_: u8 = 0;
    let mut v_r_604_: *mut LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Std_Time_Week_instDecidableLeOrdinal(v___y_601_, v___y_602_);
    lean_dec(v___y_602_);
    lean_dec(v___y_601_);
    v_r_604_ = lean_box((v_res_603_) as usize);
    return v_r_604_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal___aux__1(
    mut v_x_605_: *mut LeanObject,
    mut v_y_606_: *mut LeanObject,
) -> u8 {
    let mut v___x_607_: u8 = 0;
    v___x_607_ = lean_int_dec_lt(v_x_605_, v_y_606_);
    return v___x_607_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_608_: *mut LeanObject,
    mut v_y_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_610_: u8 = 0;
    let mut v_r_611_: *mut LeanObject = core::ptr::null_mut();
    v_res_610_ = l_Std_Time_Week_instDecidableLtOrdinal___aux__1(v_x_608_, v_y_609_);
    lean_dec(v_y_609_);
    lean_dec(v_x_608_);
    v_r_611_ = lean_box((v_res_610_) as usize);
    return v_r_611_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal(
    mut v___y_612_: *mut LeanObject,
    mut v___y_613_: *mut LeanObject,
) -> u8 {
    let mut v___x_614_: u8 = 0;
    v___x_614_ = lean_int_dec_lt(v___y_612_, v___y_613_);
    return v___x_614_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOrdinal___boxed(
    mut v___y_615_: *mut LeanObject,
    mut v___y_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_617_: u8 = 0;
    let mut v_r_618_: *mut LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Std_Time_Week_instDecidableLtOrdinal(v___y_615_, v___y_616_);
    lean_dec(v___y_616_);
    lean_dec(v___y_615_);
    v_r_618_ = lean_box((v_res_617_) as usize);
    return v_r_618_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0() -> *mut LeanObject {
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    v___x_619_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_620_ = lean_int_sub(v___x_619_, v___x_619_);
    return v___x_620_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1() -> *mut LeanObject {
    let mut v_range_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    v_range_621_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_622_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0,
    );
    v___x_623_ = lean_int_emod(v___x_622_, v_range_621_);
    return v___x_623_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2() -> *mut LeanObject {
    let mut v_range_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v_range_624_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_625_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__1,
    );
    v___x_626_ = lean_int_add(v___x_625_, v_range_624_);
    return v___x_626_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3() -> *mut LeanObject {
    let mut v_range_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    v_range_627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_628_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__2,
    );
    v___x_629_ = lean_int_emod(v___x_628_, v_range_627_);
    return v___x_629_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4() -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__3,
    );
    v___x_632_ = lean_int_add(v___x_631_, v___x_630_);
    return v___x_632_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOrdinal() -> *mut LeanObject {
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    v___x_633_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__4,
    );
    return v___x_633_;
}
pub unsafe fn l_Std_Time_Week_instOrdOrdinal___aux__1(
    mut v_x_634_: *mut LeanObject,
    mut v_y_635_: *mut LeanObject,
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
    mut v_x_641_: *mut LeanObject,
    mut v_y_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Std_Time_Week_instOrdOrdinal___aux__1(v_x_641_, v_y_642_);
    lean_dec(v_y_642_);
    lean_dec(v_x_641_);
    v_r_644_ = lean_box((v_res_643_) as usize);
    return v_r_644_;
}
pub unsafe fn l_Std_Time_Week_instReprOffset___aux__1(
    mut v_x_647_: *mut LeanObject,
    mut v_p_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    v___x_649_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_650_ = lean_int_dec_lt(v_x_647_, v___x_649_);
    if v___x_650_ == 0 {
        let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
        v___x_651_ = l_Int_repr(v_x_647_);
        v___x_652_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_652_, 0, v___x_651_);
        return v___x_652_;
    } else {
        let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
        v___x_653_ = l_Int_repr(v_x_647_);
        v___x_654_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_654_, 0, v___x_653_);
        v___x_655_ = l_Repr_addAppParen(v___x_654_, v_p_648_);
        return v___x_655_;
    }
}
pub unsafe fn l_Std_Time_Week_instReprOffset___aux__1___boxed(
    mut v_x_656_: *mut LeanObject,
    mut v_p_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_658_: *mut LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Std_Time_Week_instReprOffset___aux__1(v_x_656_, v_p_657_);
    lean_dec(v_p_657_);
    lean_dec(v_x_656_);
    return v_res_658_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset___aux__1(
    mut v_a_660_: *mut LeanObject,
    mut v_b_661_: *mut LeanObject,
) -> u8 {
    let mut v___x_662_: u8 = 0;
    v___x_662_ = lean_int_dec_eq(v_a_660_, v_b_661_);
    return v___x_662_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset___aux__1___boxed(
    mut v_a_663_: *mut LeanObject,
    mut v_b_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_665_: u8 = 0;
    let mut v_r_666_: *mut LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Std_Time_Week_instDecidableEqOffset___aux__1(v_a_663_, v_b_664_);
    lean_dec(v_b_664_);
    lean_dec(v_a_663_);
    v_r_666_ = lean_box((v_res_665_) as usize);
    return v_r_666_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v___x_668_ = lean_nat_to_int(v_a_667_);
    return v___x_668_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    v___x_670_ = lean_nat_to_int(v_a_669_);
    v___x_671_ = l_Rat_ofInt(v___x_670_);
    return v___x_671_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset(
    mut v_a_672_: *mut LeanObject,
    mut v_b_673_: *mut LeanObject,
) -> u8 {
    let mut v___x_674_: u8 = 0;
    v___x_674_ = lean_int_dec_eq(v_a_672_, v_b_673_);
    return v___x_674_;
}
pub unsafe fn l_Std_Time_Week_instDecidableEqOffset___boxed(
    mut v_a_675_: *mut LeanObject,
    mut v_b_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_677_: u8 = 0;
    let mut v_r_678_: *mut LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Std_Time_Week_instDecidableEqOffset(v_a_675_, v_b_676_);
    lean_dec(v_b_676_);
    lean_dec(v_a_675_);
    v_r_678_ = lean_box((v_res_677_) as usize);
    return v_r_678_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_679_ = lean_unsigned_to_nat(86400);
    v___x_680_ = l_Rat_instNatCast___lam__0(v___x_679_);
    return v___x_680_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1() -> *mut LeanObject {
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    v___x_681_ = lean_unsigned_to_nat(7);
    v___x_682_ = l_Rat_instNatCast___lam__0(v___x_681_);
    return v___x_682_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2() -> *mut LeanObject {
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    v___x_683_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__1,
    );
    v___x_684_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_685_ = l_Rat_mul(v___x_684_, v___x_683_);
    return v___x_685_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3() -> *mut LeanObject {
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_686_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__2,
    );
    v___x_687_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_686_);
    return v___x_687_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___aux__1() -> *mut LeanObject {
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    v___x_688_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3_once),
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1___closed__3,
    );
    return v___x_688_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__0() -> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = lean_unsigned_to_nat(86400);
    v___x_690_ =
        l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(v___x_689_);
    return v___x_690_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__1() -> *mut LeanObject {
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_691_ = lean_unsigned_to_nat(7);
    v___x_692_ =
        l_Nat_cast___at___00Std_Time_Week_instDecidableEqOffset___aux__1_spec__0(v___x_691_);
    return v___x_692_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__2() -> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    v___x_693_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__1,
    );
    v___x_694_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__0,
    );
    v___x_695_ = l_Rat_mul(v___x_694_, v___x_693_);
    return v___x_695_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset___closed__3() -> *mut LeanObject {
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___x_696_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__2_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__2,
    );
    v___x_697_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_696_);
    return v___x_697_;
}
pub unsafe fn _init_l_Std_Time_Week_instInhabitedOffset() -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOffset___closed__3_once),
        _init_l_Std_Time_Week_instInhabitedOffset___closed__3,
    );
    return v___x_698_;
}
pub unsafe fn l_Std_Time_Week_instAddOffset___aux__1(
    mut v_u1_699_: *mut LeanObject,
    mut v_u2_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    v___x_701_ = lean_int_add(v_u1_699_, v_u2_700_);
    return v___x_701_;
}
pub unsafe fn l_Std_Time_Week_instAddOffset___aux__1___boxed(
    mut v_u1_702_: *mut LeanObject,
    mut v_u2_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Std_Time_Week_instAddOffset___aux__1(v_u1_702_, v_u2_703_);
    lean_dec(v_u2_703_);
    lean_dec(v_u1_702_);
    return v_res_704_;
}
pub unsafe fn l_Std_Time_Week_instSubOffset___aux__1(
    mut v_u1_707_: *mut LeanObject,
    mut v_u2_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_int_sub(v_u1_707_, v_u2_708_);
    return v___x_709_;
}
pub unsafe fn l_Std_Time_Week_instSubOffset___aux__1___boxed(
    mut v_u1_710_: *mut LeanObject,
    mut v_u2_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_712_: *mut LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Std_Time_Week_instSubOffset___aux__1(v_u1_710_, v_u2_711_);
    lean_dec(v_u2_711_);
    lean_dec(v_u1_710_);
    return v_res_712_;
}
pub unsafe fn l_Std_Time_Week_instNegOffset___aux__1(
    mut v_x_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_716_ = lean_int_neg(v_x_715_);
    return v___x_716_;
}
pub unsafe fn l_Std_Time_Week_instNegOffset___aux__1___boxed(
    mut v_x_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Std_Time_Week_instNegOffset___aux__1(v_x_717_);
    lean_dec(v_x_717_);
    return v_res_718_;
}
pub unsafe fn _init_l_Std_Time_Week_instLEOffset() -> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = lean_box(0);
    return v___x_721_;
}
pub unsafe fn _init_l_Std_Time_Week_instLTOffset() -> *mut LeanObject {
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    v___x_722_ = lean_box(0);
    return v___x_722_;
}
pub unsafe fn l_Std_Time_Week_instToStringOffset___aux__1(
    mut v_n_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = l_Int_repr(v_n_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_Week_instToStringOffset___aux__1___boxed(
    mut v_n_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_726_: *mut LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Std_Time_Week_instToStringOffset___aux__1(v_n_725_);
    lean_dec(v_n_725_);
    return v_res_726_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset___aux__1(
    mut v_x_729_: *mut LeanObject,
    mut v_y_730_: *mut LeanObject,
) -> u8 {
    let mut v___x_731_: u8 = 0;
    v___x_731_ = lean_int_dec_le(v_x_729_, v_y_730_);
    return v___x_731_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset___aux__1___boxed(
    mut v_x_732_: *mut LeanObject,
    mut v_y_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_734_: u8 = 0;
    let mut v_r_735_: *mut LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Std_Time_Week_instDecidableLeOffset___aux__1(v_x_732_, v_y_733_);
    lean_dec(v_y_733_);
    lean_dec(v_x_732_);
    v_r_735_ = lean_box((v_res_734_) as usize);
    return v_r_735_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset(
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
) -> u8 {
    let mut v___x_738_: u8 = 0;
    v___x_738_ = lean_int_dec_le(v___y_736_, v___y_737_);
    return v___x_738_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLeOffset___boxed(
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_741_: u8 = 0;
    let mut v_r_742_: *mut LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Std_Time_Week_instDecidableLeOffset(v___y_739_, v___y_740_);
    lean_dec(v___y_740_);
    lean_dec(v___y_739_);
    v_r_742_ = lean_box((v_res_741_) as usize);
    return v_r_742_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset___aux__1(
    mut v_x_743_: *mut LeanObject,
    mut v_y_744_: *mut LeanObject,
) -> u8 {
    let mut v___x_745_: u8 = 0;
    v___x_745_ = lean_int_dec_lt(v_x_743_, v_y_744_);
    return v___x_745_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset___aux__1___boxed(
    mut v_x_746_: *mut LeanObject,
    mut v_y_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_748_: u8 = 0;
    let mut v_r_749_: *mut LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Std_Time_Week_instDecidableLtOffset___aux__1(v_x_746_, v_y_747_);
    lean_dec(v_y_747_);
    lean_dec(v_x_746_);
    v_r_749_ = lean_box((v_res_748_) as usize);
    return v_r_749_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset(
    mut v___y_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
) -> u8 {
    let mut v___x_752_: u8 = 0;
    v___x_752_ = lean_int_dec_lt(v___y_750_, v___y_751_);
    return v___x_752_;
}
pub unsafe fn l_Std_Time_Week_instDecidableLtOffset___boxed(
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_755_: u8 = 0;
    let mut v_r_756_: *mut LeanObject = core::ptr::null_mut();
    v_res_755_ = l_Std_Time_Week_instDecidableLtOffset(v___y_753_, v___y_754_);
    lean_dec(v___y_754_);
    lean_dec(v___y_753_);
    v_r_756_ = lean_box((v_res_755_) as usize);
    return v_r_756_;
}
pub unsafe fn l_Std_Time_Week_instOfNatOffset(mut v_n_757_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_nat_to_int(v_n_757_);
    return v___x_758_;
}
pub unsafe fn l_Std_Time_Week_instOrdOffset___aux__1(
    mut v_x_759_: *mut LeanObject,
    mut v_y_760_: *mut LeanObject,
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
    mut v_x_766_: *mut LeanObject,
    mut v_y_767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_768_: u8 = 0;
    let mut v_r_769_: *mut LeanObject = core::ptr::null_mut();
    v_res_768_ = l_Std_Time_Week_instOrdOffset___aux__1(v_x_766_, v_y_767_);
    lean_dec(v_y_767_);
    lean_dec(v_x_766_);
    v_r_769_ = lean_box((v_res_768_) as usize);
    return v_r_769_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt___redArg(
    mut v_data_772_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_772_);
    return v_data_772_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt___redArg___boxed(
    mut v_data_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l_Std_Time_Week_Ordinal_ofInt___redArg(v_data_773_);
    lean_dec(v_data_773_);
    return v_res_774_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt(
    mut v_data_775_: *mut LeanObject,
    mut v_h_776_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_775_);
    return v_data_775_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofInt___boxed(
    mut v_data_777_: *mut LeanObject,
    mut v_h_778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_779_: *mut LeanObject = core::ptr::null_mut();
    v_res_779_ = l_Std_Time_Week_Ordinal_ofInt(v_data_777_, v_h_778_);
    lean_dec(v_data_777_);
    return v_res_779_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(
    mut v_n_780_: *mut LeanObject,
    mut v_a_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    v___x_782_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instReprOrdinal___aux__1___closed__0,
    );
    v___x_783_ = lean_int_dec_lt(v_n_780_, v___x_782_);
    if v___x_783_ == 0 {
        let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
        v___x_784_ = l_Int_repr(v_n_780_);
        v___x_785_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_785_, 0, v___x_784_);
        return v___x_785_;
    } else {
        let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
        v___x_786_ = l_Int_repr(v_n_780_);
        v___x_787_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_787_, 0, v___x_786_);
        v___x_788_ = l_Repr_addAppParen(v___x_787_, v_a_781_);
        return v___x_788_;
    }
}
pub unsafe fn l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1___boxed(
    mut v_n_789_: *mut LeanObject,
    mut v_a_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Std_Time_Week_Ordinal_instReprOfMonth___aux__1(v_n_789_, v_a_790_);
    lean_dec(v_a_790_);
    lean_dec(v_n_789_);
    return v_res_791_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(
    mut v_a_793_: *mut LeanObject,
    mut v_b_794_: *mut LeanObject,
) -> u8 {
    let mut v___x_795_: u8 = 0;
    v___x_795_ = lean_int_dec_eq(v_a_793_, v_b_794_);
    return v___x_795_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1___boxed(
    mut v_a_796_: *mut LeanObject,
    mut v_b_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_798_: u8 = 0;
    let mut v_r_799_: *mut LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___aux__1(v_a_796_, v_b_797_);
    lean_dec(v_b_797_);
    lean_dec(v_a_796_);
    v_r_799_ = lean_box((v_res_798_) as usize);
    return v_r_799_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(
    mut v_a_800_: *mut LeanObject,
    mut v_b_801_: *mut LeanObject,
) -> u8 {
    let mut v___x_802_: u8 = 0;
    v___x_802_ = lean_int_dec_eq(v_a_800_, v_b_801_);
    return v___x_802_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instDecidableEqOfMonth___boxed(
    mut v_a_803_: *mut LeanObject,
    mut v_b_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_805_: u8 = 0;
    let mut v_r_806_: *mut LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Std_Time_Week_Ordinal_instDecidableEqOfMonth(v_a_803_, v_b_804_);
    lean_dec(v_b_804_);
    lean_dec(v_a_803_);
    v_r_806_ = lean_box((v_res_805_) as usize);
    return v_r_806_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0()
-> *mut LeanObject {
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_807_ = lean_unsigned_to_nat(5);
    v___x_808_ = lean_nat_to_int(v___x_807_);
    return v___x_808_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1()
-> *mut LeanObject {
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_809_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__0,
    );
    v___x_810_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_811_ = lean_int_add(v___x_810_, v___x_809_);
    return v___x_811_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2()
-> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__1,
    );
    v___x_814_ = lean_int_sub(v___x_813_, v___x_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3()
-> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_815_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_816_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__2,
    );
    v_range_817_ = lean_int_add(v___x_816_, v___x_815_);
    return v_range_817_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1(
    mut v_n_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    v___x_819_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_820_ = lean_nat_to_int(v_n_818_);
    v_range_821_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_822_ = lean_int_sub(v___x_820_, v___x_819_);
    lean_dec(v___x_820_);
    v___x_823_ = lean_int_emod(v___x_822_, v_range_821_);
    lean_dec(v___x_822_);
    v___x_824_ = lean_int_add(v___x_823_, v_range_821_);
    lean_dec(v___x_823_);
    v___x_825_ = lean_int_emod(v___x_824_, v_range_821_);
    lean_dec(v___x_824_);
    v___x_826_ = lean_int_add(v___x_825_, v___x_819_);
    lean_dec(v___x_825_);
    return v___x_826_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOfNatOfMonth(
    mut v_n_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_828_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_829_ = lean_nat_to_int(v_n_827_);
    v_range_830_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_831_ = lean_int_sub(v___x_829_, v___x_828_);
    lean_dec(v___x_829_);
    v___x_832_ = lean_int_emod(v___x_831_, v_range_830_);
    lean_dec(v___x_831_);
    v___x_833_ = lean_int_add(v___x_832_, v_range_830_);
    lean_dec(v___x_832_);
    v___x_834_ = lean_int_emod(v___x_833_, v_range_830_);
    lean_dec(v___x_833_);
    v___x_835_ = lean_int_add(v___x_834_, v___x_828_);
    lean_dec(v___x_834_);
    return v___x_835_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0() -> *mut LeanObject {
    let mut v_range_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    v_range_836_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_837_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Week_instInhabitedOrdinal___closed__0,
    );
    v___x_838_ = lean_int_emod(v___x_837_, v_range_836_);
    return v___x_838_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1() -> *mut LeanObject {
    let mut v_range_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    v_range_839_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_840_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__0,
    );
    v___x_841_ = lean_int_add(v___x_840_, v_range_839_);
    return v___x_841_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2() -> *mut LeanObject {
    let mut v_range_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    v_range_842_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instOfNatOfMonth___aux__1___closed__3,
    );
    v___x_843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__1,
    );
    v___x_844_ = lean_int_emod(v___x_843_, v_range_842_);
    return v___x_844_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3() -> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_845_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Week_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_846_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__2,
    );
    v___x_847_ = lean_int_add(v___x_846_, v___x_845_);
    return v___x_847_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth() -> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3_once),
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth___closed__3,
    );
    return v___x_848_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(
    mut v_x_849_: *mut LeanObject,
    mut v_y_850_: *mut LeanObject,
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
    mut v_x_856_: *mut LeanObject,
    mut v_y_857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_858_: u8 = 0;
    let mut v_r_859_: *mut LeanObject = core::ptr::null_mut();
    v_res_858_ = l_Std_Time_Week_Ordinal_instOrdOfMonth___aux__1(v_x_856_, v_y_857_);
    lean_dec(v_y_857_);
    lean_dec(v_x_856_);
    v_r_859_ = lean_box((v_res_858_) as usize);
    return v_r_859_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__10;
    v___x_889_ = l_Lean_mkAtom(v___x_888_);
    return v___x_889_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__12,
    );
    v___x_891_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_892_ = lean_array_push(v___x_891_, v___x_890_);
    return v___x_892_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__16;
    v___x_904_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_905_ = lean_array_push(v___x_904_, v___x_903_);
    return v___x_905_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    v___x_906_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__17,
    );
    v___x_907_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__15;
    v___x_908_ = lean_box(2);
    v___x_909_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_909_, 0, v___x_908_);
    lean_ctor_set(v___x_909_, 1, v___x_907_);
    lean_ctor_set(v___x_909_, 2, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__18,
    );
    v___x_911_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__13,
    );
    v___x_912_ = lean_array_push(v___x_911_, v___x_910_);
    return v___x_912_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__19,
    );
    v___x_914_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__11;
    v___x_915_ = lean_box(2);
    v___x_916_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_916_, 0, v___x_915_);
    lean_ctor_set(v___x_916_, 1, v___x_914_);
    lean_ctor_set(v___x_916_, 2, v___x_913_);
    return v___x_916_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_917_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__20,
    );
    v___x_918_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_919_ = lean_array_push(v___x_918_, v___x_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__21,
    );
    v___x_921_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__9;
    v___x_922_ = lean_box(2);
    v___x_923_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_923_, 0, v___x_922_);
    lean_ctor_set(v___x_923_, 1, v___x_921_);
    lean_ctor_set(v___x_923_, 2, v___x_920_);
    return v___x_923_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__22,
    );
    v___x_925_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_926_ = lean_array_push(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__23,
    );
    v___x_928_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__7;
    v___x_929_ = lean_box(2);
    v___x_930_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_930_, 0, v___x_929_);
    lean_ctor_set(v___x_930_, 1, v___x_928_);
    lean_ctor_set(v___x_930_, 2, v___x_927_);
    return v___x_930_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    v___x_931_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__24,
    );
    v___x_932_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__5;
    v___x_933_ = lean_array_push(v___x_932_, v___x_931_);
    return v___x_933_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    v___x_934_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__25,
    );
    v___x_935_ = l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__4;
    v___x_936_ = lean_box(2);
    v___x_937_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_937_, 0, v___x_936_);
    lean_ctor_set(v___x_937_, 1, v___x_935_);
    lean_ctor_set(v___x_937_, 2, v___x_934_);
    return v___x_937_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofNat___auto__1() -> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    v___x_938_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26_once),
        _init_l_Std_Time_Week_Ordinal_ofNat___auto__1___closed__26,
    );
    return v___x_938_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofNat___redArg(
    mut v_data_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    v___x_940_ = lean_nat_to_int(v_data_939_);
    return v___x_940_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofNat(
    mut v_data_941_: *mut LeanObject,
    mut v_h_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = lean_nat_to_int(v_data_941_);
    return v___x_943_;
}
pub unsafe fn _init_l_Std_Time_Week_Ordinal_ofFin___closed__0() -> *mut LeanObject {
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    v___x_944_ = lean_unsigned_to_nat(1);
    v___x_945_ = lean_nat_to_int(v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_ofFin(mut v_data_946_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    v___x_947_ = lean_unsigned_to_nat(1);
    v___x_948_ = lean_nat_dec_le(v___x_947_, v_data_946_);
    if v___x_948_ == 0 {
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_data_946_);
        v___x_949_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofFin___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_Week_Ordinal_ofFin___closed__0_once),
            _init_l_Std_Time_Week_Ordinal_ofFin___closed__0,
        );
        return v___x_949_;
    } else {
        let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
        v___x_950_ = lean_nat_to_int(v_data_946_);
        return v___x_950_;
    }
}
pub unsafe fn l_Std_Time_Week_Ordinal_toOffset(
    mut v_ordinal_951_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ordinal_951_);
    return v_ordinal_951_;
}
pub unsafe fn l_Std_Time_Week_Ordinal_toOffset___boxed(
    mut v_ordinal_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_953_: *mut LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Std_Time_Week_Ordinal_toOffset(v_ordinal_952_);
    lean_dec(v_ordinal_952_);
    return v_res_953_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofNat(mut v_data_954_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    v___x_955_ = lean_nat_to_int(v_data_954_);
    return v___x_955_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofInt(mut v_data_956_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_data_956_);
    return v_data_956_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofInt___boxed(
    mut v_data_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_958_: *mut LeanObject = core::ptr::null_mut();
    v_res_958_ = l_Std_Time_Week_Offset_ofInt(v_data_957_);
    lean_dec(v_data_957_);
    return v_res_958_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    v___x_959_ = lean_unsigned_to_nat(604800000);
    v___x_960_ = lean_nat_to_int(v___x_959_);
    return v___x_960_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMilliseconds(
    mut v_weeks_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    v___x_962_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0,
    );
    v___x_963_ = lean_int_mul(v_weeks_961_, v___x_962_);
    return v___x_963_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMilliseconds___boxed(
    mut v_weeks_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_965_: *mut LeanObject = core::ptr::null_mut();
    v_res_965_ = l_Std_Time_Week_Offset_toMilliseconds(v_weeks_964_);
    lean_dec(v_weeks_964_);
    return v_res_965_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMilliseconds(
    mut v_millis_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMilliseconds___closed__0,
    );
    v___x_968_ = lean_int_ediv(v_millis_966_, v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMilliseconds___boxed(
    mut v_millis_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_970_: *mut LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Std_Time_Week_Offset_ofMilliseconds(v_millis_969_);
    lean_dec(v_millis_969_);
    return v_res_970_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0() -> *mut LeanObject {
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    v___x_971_ = lean_cstr_to_nat(b"604800000000000\0".as_ptr().cast());
    v___x_972_ = lean_nat_to_int(v___x_971_);
    return v___x_972_;
}
pub unsafe fn l_Std_Time_Week_Offset_toNanoseconds(
    mut v_weeks_973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    v___x_974_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0,
    );
    v___x_975_ = lean_int_mul(v_weeks_973_, v___x_974_);
    return v___x_975_;
}
pub unsafe fn l_Std_Time_Week_Offset_toNanoseconds___boxed(
    mut v_weeks_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_977_: *mut LeanObject = core::ptr::null_mut();
    v_res_977_ = l_Std_Time_Week_Offset_toNanoseconds(v_weeks_976_);
    lean_dec(v_weeks_976_);
    return v_res_977_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofNanoseconds(
    mut v_nanos_978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    v___x_979_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toNanoseconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toNanoseconds___closed__0,
    );
    v___x_980_ = lean_int_ediv(v_nanos_978_, v___x_979_);
    return v___x_980_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofNanoseconds___boxed(
    mut v_nanos_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Std_Time_Week_Offset_ofNanoseconds(v_nanos_981_);
    lean_dec(v_nanos_981_);
    return v_res_982_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toSeconds___closed__0() -> *mut LeanObject {
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    v___x_983_ = lean_unsigned_to_nat(604800);
    v___x_984_ = lean_nat_to_int(v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Std_Time_Week_Offset_toSeconds(
    mut v_weeks_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    v___x_986_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toSeconds___closed__0,
    );
    v___x_987_ = lean_int_mul(v_weeks_985_, v___x_986_);
    return v___x_987_;
}
pub unsafe fn l_Std_Time_Week_Offset_toSeconds___boxed(
    mut v_weeks_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_989_: *mut LeanObject = core::ptr::null_mut();
    v_res_989_ = l_Std_Time_Week_Offset_toSeconds(v_weeks_988_);
    lean_dec(v_weeks_988_);
    return v_res_989_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofSeconds(
    mut v_secs_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_991_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Week_Offset_toSeconds___closed__0,
    );
    v___x_992_ = lean_int_ediv(v_secs_990_, v___x_991_);
    return v___x_992_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofSeconds___boxed(
    mut v_secs_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Std_Time_Week_Offset_ofSeconds(v_secs_993_);
    lean_dec(v_secs_993_);
    return v_res_994_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_995_ = lean_unsigned_to_nat(10080);
    v___x_996_ = lean_nat_to_int(v___x_995_);
    return v___x_996_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMinutes(
    mut v_weeks_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    v___x_998_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMinutes___closed__0,
    );
    v___x_999_ = lean_int_mul(v_weeks_997_, v___x_998_);
    return v___x_999_;
}
pub unsafe fn l_Std_Time_Week_Offset_toMinutes___boxed(
    mut v_weeks_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1001_: *mut LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Std_Time_Week_Offset_toMinutes(v_weeks_1000_);
    lean_dec(v_weeks_1000_);
    return v_res_1001_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMinutes(
    mut v_minutes_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    v___x_1003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Week_Offset_toMinutes___closed__0,
    );
    v___x_1004_ = lean_int_ediv(v_minutes_1002_, v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofMinutes___boxed(
    mut v_minutes_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1006_: *mut LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Std_Time_Week_Offset_ofMinutes(v_minutes_1005_);
    lean_dec(v_minutes_1005_);
    return v_res_1006_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toHours___closed__0() -> *mut LeanObject {
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    v___x_1007_ = lean_unsigned_to_nat(168);
    v___x_1008_ = lean_nat_to_int(v___x_1007_);
    return v___x_1008_;
}
pub unsafe fn l_Std_Time_Week_Offset_toHours(
    mut v_weeks_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Week_Offset_toHours___closed__0,
    );
    v___x_1011_ = lean_int_mul(v_weeks_1009_, v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Std_Time_Week_Offset_toHours___boxed(
    mut v_weeks_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Std_Time_Week_Offset_toHours(v_weeks_1012_);
    lean_dec(v_weeks_1012_);
    return v_res_1013_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofHours(
    mut v_hours_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___x_1015_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Week_Offset_toHours___closed__0,
    );
    v___x_1016_ = lean_int_ediv(v_hours_1014_, v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofHours___boxed(
    mut v_hours_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_Time_Week_Offset_ofHours(v_hours_1017_);
    lean_dec(v_hours_1017_);
    return v_res_1018_;
}
pub unsafe fn _init_l_Std_Time_Week_Offset_toDays___closed__0() -> *mut LeanObject {
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    v___x_1019_ = lean_unsigned_to_nat(7);
    v___x_1020_ = lean_nat_to_int(v___x_1019_);
    return v___x_1020_;
}
pub unsafe fn l_Std_Time_Week_Offset_toDays(mut v_weeks_1021_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v___x_1022_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Week_Offset_toDays___closed__0,
    );
    v___x_1023_ = lean_int_mul(v_weeks_1021_, v___x_1022_);
    return v___x_1023_;
}
pub unsafe fn l_Std_Time_Week_Offset_toDays___boxed(
    mut v_weeks_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1025_ = l_Std_Time_Week_Offset_toDays(v_weeks_1024_);
    lean_dec(v_weeks_1024_);
    return v_res_1025_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofDays(mut v_days_1026_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    v___x_1027_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Week_Offset_toDays___closed__0_once),
        _init_l_Std_Time_Week_Offset_toDays___closed__0,
    );
    v___x_1028_ = lean_int_ediv(v_days_1026_, v___x_1027_);
    return v___x_1028_;
}
pub unsafe fn l_Std_Time_Week_Offset_ofDays___boxed(
    mut v_days_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Std_Time_Week_Offset_ofDays(v_days_1029_);
    lean_dec(v_days_1029_);
    return v_res_1030_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Week(builtin: u8) -> *mut LeanObject {
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
    l_Std_Time_Week_instLEOrdinal = _init_l_Std_Time_Week_instLEOrdinal();
    lean_mark_persistent(l_Std_Time_Week_instLEOrdinal);
    l_Std_Time_Week_instLTOrdinal = _init_l_Std_Time_Week_instLTOrdinal();
    lean_mark_persistent(l_Std_Time_Week_instLTOrdinal);
    l_Std_Time_Week_instInhabitedOrdinal = _init_l_Std_Time_Week_instInhabitedOrdinal();
    lean_mark_persistent(l_Std_Time_Week_instInhabitedOrdinal);
    l_Std_Time_Week_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Week_instInhabitedOffset___aux__1();
    lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset___aux__1);
    l_Std_Time_Week_instInhabitedOffset = _init_l_Std_Time_Week_instInhabitedOffset();
    lean_mark_persistent(l_Std_Time_Week_instInhabitedOffset);
    l_Std_Time_Week_instLEOffset = _init_l_Std_Time_Week_instLEOffset();
    lean_mark_persistent(l_Std_Time_Week_instLEOffset);
    l_Std_Time_Week_instLTOffset = _init_l_Std_Time_Week_instLTOffset();
    lean_mark_persistent(l_Std_Time_Week_instLTOffset);
    l_Std_Time_Week_Ordinal_instInhabitedOfMonth =
        _init_l_Std_Time_Week_Ordinal_instInhabitedOfMonth();
    lean_mark_persistent(l_Std_Time_Week_Ordinal_instInhabitedOfMonth);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Week(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Time_Week_Ordinal_ofNat___auto__1 = _init_l_Std_Time_Week_Ordinal_ofNat___auto__1();
    lean_mark_persistent(l_Std_Time_Week_Ordinal_ofNat___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_Unit_Week(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Time_Date_Unit_Week(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Week(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Week(builtin);
}
