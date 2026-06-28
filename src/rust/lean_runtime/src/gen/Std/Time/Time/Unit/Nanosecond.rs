// Lean compiler output
// Module: Std.Time.Time.Unit.Nanosecond
// Imports: Std.Time.Internal
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_instNatCast___lam__0, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::r#gen::Std::Time::Internal::{
    initialize_Std_Time_Internal, runtime_initialize_Std_Time_Internal,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_mod;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Nanosecond_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Nanosecond_instReprOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instReprOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instLEOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instLTOrdinal: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instInhabitedOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Nanosecond_instOrdOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instOrdOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instReprOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instInhabitedOffset___aux__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_instInhabitedOffset___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instInhabitedOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Nanosecond_instAddOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Nanosecond_instAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Nanosecond_instSubOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Nanosecond_instSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Nanosecond_instNegOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Nanosecond_instNegOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instNegOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instNegOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instNegOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instLEOffset: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instLTOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Nanosecond_instToStringOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Nanosecond_instToStringOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instToStringOffset___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instToStringOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instToStringOffset___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_Nanosecond_instOrdOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Nanosecond_instOrdOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instOrdOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instOrdOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instOrdOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instReprSpan: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instLESpan: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instLTSpan: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_instInhabitedSpan: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Nanosecond_instOrdSpan___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Nanosecond_instOrdSpan___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instOrdSpan___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_instOrdSpan: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instOrdSpan___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_Ordinal_instReprOfDay: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_Ordinal_instLEOfDay: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_Ordinal_instLTOfDay: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_Nanosecond_Ordinal_instOrdOfDay: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0() -> *mut LeanObject
{
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_unsigned_to_nat(0);
    v___x_392_ = lean_nat_to_int(v___x_391_);
    return v___x_392_;
}
pub unsafe fn l_Std_Time_Nanosecond_instReprOrdinal___aux__1(
    mut v_n_393_: *mut LeanObject,
    mut v_a_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u8 = 0;
    v___x_395_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_396_ = lean_int_dec_lt(v_n_393_, v___x_395_);
    if v___x_396_ == 0 {
        let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
        v___x_397_ = l_Int_repr(v_n_393_);
        v___x_398_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_398_, 0, v___x_397_);
        return v___x_398_;
    } else {
        let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
        v___x_399_ = l_Int_repr(v_n_393_);
        v___x_400_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_400_, 0, v___x_399_);
        v___x_401_ = l_Repr_addAppParen(v___x_400_, v_a_394_);
        return v___x_401_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instReprOrdinal___aux__1___boxed(
    mut v_n_402_: *mut LeanObject,
    mut v_a_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_404_: *mut LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Std_Time_Nanosecond_instReprOrdinal___aux__1(v_n_402_, v_a_403_);
    lean_dec(v_a_403_);
    lean_dec(v_n_402_);
    return v_res_404_;
}
pub unsafe fn l_Std_Time_Nanosecond_instReprOrdinal___lam__0(
    mut v___y_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: u8 = 0;
    v___x_407_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_408_ = lean_int_dec_lt(v___y_405_, v___x_407_);
    if v___x_408_ == 0 {
        let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
        v___x_409_ = l_Int_repr(v___y_405_);
        v___x_410_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_410_, 0, v___x_409_);
        return v___x_410_;
    } else {
        let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
        v___x_411_ = l_Int_repr(v___y_405_);
        v___x_412_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_412_, 0, v___x_411_);
        v___x_413_ = l_Repr_addAppParen(v___x_412_, v___y_406_);
        return v___x_413_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instReprOrdinal___lam__0___boxed(
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v___y_414_, v___y_415_);
    lean_dec(v___y_415_);
    lean_dec(v___y_414_);
    return v_res_416_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(
    mut v_a_419_: *mut LeanObject,
    mut v_b_420_: *mut LeanObject,
) -> u8 {
    let mut v___x_421_: u8 = 0;
    v___x_421_ = lean_int_dec_eq(v_a_419_, v_b_420_);
    return v___x_421_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_422_: *mut LeanObject,
    mut v_b_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_424_: u8 = 0;
    let mut v_r_425_: *mut LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal___aux__1(v_a_422_, v_b_423_);
    lean_dec(v_b_423_);
    lean_dec(v_a_422_);
    v_r_425_ = lean_box((v_res_424_) as usize);
    return v_r_425_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOrdinal(
    mut v_a_426_: *mut LeanObject,
    mut v_b_427_: *mut LeanObject,
) -> u8 {
    let mut v___x_428_: u8 = 0;
    v___x_428_ = lean_int_dec_eq(v_a_426_, v_b_427_);
    return v___x_428_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOrdinal___boxed(
    mut v_a_429_: *mut LeanObject,
    mut v_b_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Std_Time_Nanosecond_instDecidableEqOrdinal(v_a_429_, v_b_430_);
    lean_dec(v_b_430_);
    lean_dec(v_a_429_);
    v_r_432_ = lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instLEOrdinal() -> *mut LeanObject {
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_box(0);
    return v___x_433_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instLTOrdinal() -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_box(0);
    return v___x_434_;
}
pub unsafe fn l_Std_Time_Nanosecond_instOfNatOrdinal(
    mut v_n_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_436_ = lean_unsigned_to_nat(1000000000);
    v___x_437_ = lean_nat_mod(v_n_435_, v___x_436_);
    v___x_438_ = lean_nat_to_int(v___x_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Time_Nanosecond_instOfNatOrdinal___boxed(
    mut v_n_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_440_: *mut LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Std_Time_Nanosecond_instOfNatOrdinal(v_n_439_);
    lean_dec(v_n_439_);
    return v_res_440_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0() -> *mut LeanObject {
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_441_ = lean_unsigned_to_nat(1000000000);
    v___x_442_ = lean_unsigned_to_nat(0);
    v___x_443_ = lean_nat_mod(v___x_442_, v___x_441_);
    return v___x_443_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1() -> *mut LeanObject {
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_444_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__0,
    );
    v___x_445_ = lean_nat_to_int(v___x_444_);
    return v___x_445_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOrdinal() -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Nanosecond_instInhabitedOrdinal___closed__1,
    );
    return v___x_446_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(
    mut v_x_447_: *mut LeanObject,
    mut v_y_448_: *mut LeanObject,
) -> u8 {
    let mut v___x_449_: u8 = 0;
    v___x_449_ = lean_int_dec_le(v_x_447_, v_y_448_);
    return v___x_449_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_450_: *mut LeanObject,
    mut v_y_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_452_: u8 = 0;
    let mut v_r_453_: *mut LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal___aux__1(v_x_450_, v_y_451_);
    lean_dec(v_y_451_);
    lean_dec(v_x_450_);
    v_r_453_ = lean_box((v_res_452_) as usize);
    return v_r_453_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOrdinal(
    mut v___y_454_: *mut LeanObject,
    mut v___y_455_: *mut LeanObject,
) -> u8 {
    let mut v___x_456_: u8 = 0;
    v___x_456_ = lean_int_dec_le(v___y_454_, v___y_455_);
    return v___x_456_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOrdinal___boxed(
    mut v___y_457_: *mut LeanObject,
    mut v___y_458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_459_: u8 = 0;
    let mut v_r_460_: *mut LeanObject = core::ptr::null_mut();
    v_res_459_ = l_Std_Time_Nanosecond_instDecidableLeOrdinal(v___y_457_, v___y_458_);
    lean_dec(v___y_458_);
    lean_dec(v___y_457_);
    v_r_460_ = lean_box((v_res_459_) as usize);
    return v_r_460_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(
    mut v_x_461_: *mut LeanObject,
    mut v_y_462_: *mut LeanObject,
) -> u8 {
    let mut v___x_463_: u8 = 0;
    v___x_463_ = lean_int_dec_lt(v_x_461_, v_y_462_);
    return v___x_463_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_464_: *mut LeanObject,
    mut v_y_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_466_: u8 = 0;
    let mut v_r_467_: *mut LeanObject = core::ptr::null_mut();
    v_res_466_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal___aux__1(v_x_464_, v_y_465_);
    lean_dec(v_y_465_);
    lean_dec(v_x_464_);
    v_r_467_ = lean_box((v_res_466_) as usize);
    return v_r_467_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOrdinal(
    mut v___y_468_: *mut LeanObject,
    mut v___y_469_: *mut LeanObject,
) -> u8 {
    let mut v___x_470_: u8 = 0;
    v___x_470_ = lean_int_dec_lt(v___y_468_, v___y_469_);
    return v___x_470_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOrdinal___boxed(
    mut v___y_471_: *mut LeanObject,
    mut v___y_472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_473_: u8 = 0;
    let mut v_r_474_: *mut LeanObject = core::ptr::null_mut();
    v_res_473_ = l_Std_Time_Nanosecond_instDecidableLtOrdinal(v___y_471_, v___y_472_);
    lean_dec(v___y_472_);
    lean_dec(v___y_471_);
    v_r_474_ = lean_box((v_res_473_) as usize);
    return v_r_474_;
}
pub unsafe fn l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(
    mut v_x_475_: *mut LeanObject,
    mut v_y_476_: *mut LeanObject,
) -> u8 {
    let mut v___x_477_: u8 = 0;
    v___x_477_ = lean_int_dec_lt(v_x_475_, v_y_476_);
    if v___x_477_ == 0 {
        let mut v___x_478_: u8 = 0;
        v___x_478_ = lean_int_dec_eq(v_x_475_, v_y_476_);
        if v___x_478_ == 0 {
            let mut v___x_479_: u8 = 0;
            v___x_479_ = 2;
            return v___x_479_;
        } else {
            let mut v___x_480_: u8 = 0;
            v___x_480_ = 1;
            return v___x_480_;
        }
    } else {
        let mut v___x_481_: u8 = 0;
        v___x_481_ = 0;
        return v___x_481_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed(
    mut v_x_482_: *mut LeanObject,
    mut v_y_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: u8 = 0;
    let mut v_r_485_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Std_Time_Nanosecond_instOrdOrdinal___aux__1(v_x_482_, v_y_483_);
    lean_dec(v_y_483_);
    lean_dec(v_x_482_);
    v_r_485_ = lean_box((v_res_484_) as usize);
    return v_r_485_;
}
pub unsafe fn l_Std_Time_Nanosecond_instReprOffset___aux__1(
    mut v_x_488_: *mut LeanObject,
    mut v_p_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    v___x_490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_491_ = lean_int_dec_lt(v_x_488_, v___x_490_);
    if v___x_491_ == 0 {
        let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
        v___x_492_ = l_Int_repr(v_x_488_);
        v___x_493_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_493_, 0, v___x_492_);
        return v___x_493_;
    } else {
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
        v___x_494_ = l_Int_repr(v_x_488_);
        v___x_495_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_495_, 0, v___x_494_);
        v___x_496_ = l_Repr_addAppParen(v___x_495_, v_p_489_);
        return v___x_496_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instReprOffset___aux__1___boxed(
    mut v_x_497_: *mut LeanObject,
    mut v_p_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Std_Time_Nanosecond_instReprOffset___aux__1(v_x_497_, v_p_498_);
    lean_dec(v_p_498_);
    lean_dec(v_x_497_);
    return v_res_499_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(
    mut v_a_501_: *mut LeanObject,
    mut v_b_502_: *mut LeanObject,
) -> u8 {
    let mut v___x_503_: u8 = 0;
    v___x_503_ = lean_int_dec_eq(v_a_501_, v_b_502_);
    return v___x_503_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1___boxed(
    mut v_a_504_: *mut LeanObject,
    mut v_b_505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_506_: u8 = 0;
    let mut v_r_507_: *mut LeanObject = core::ptr::null_mut();
    v_res_506_ = l_Std_Time_Nanosecond_instDecidableEqOffset___aux__1(v_a_504_, v_b_505_);
    lean_dec(v_b_505_);
    lean_dec(v_a_504_);
    v_r_507_ = lean_box((v_res_506_) as usize);
    return v_r_507_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    v___x_509_ = lean_nat_to_int(v_a_508_);
    return v___x_509_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_nat_to_int(v_a_510_);
    v___x_512_ = l_Rat_ofInt(v___x_511_);
    return v___x_512_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOffset(
    mut v_a_513_: *mut LeanObject,
    mut v_b_514_: *mut LeanObject,
) -> u8 {
    let mut v___x_515_: u8 = 0;
    v___x_515_ = lean_int_dec_eq(v_a_513_, v_b_514_);
    return v___x_515_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqOffset___boxed(
    mut v_a_516_: *mut LeanObject,
    mut v_b_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_518_: u8 = 0;
    let mut v_r_519_: *mut LeanObject = core::ptr::null_mut();
    v_res_518_ = l_Std_Time_Nanosecond_instDecidableEqOffset(v_a_516_, v_b_517_);
    lean_dec(v_b_517_);
    lean_dec(v_a_516_);
    v_r_519_ = lean_box((v_res_518_) as usize);
    return v_r_519_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0()
-> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    v___x_520_ = lean_unsigned_to_nat(1);
    v___x_521_ = l_Rat_instNatCast___lam__0(v___x_520_);
    return v___x_521_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1()
-> *mut LeanObject {
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    v___x_522_ = lean_unsigned_to_nat(1000000000);
    v___x_523_ = l_Rat_instNatCast___lam__0(v___x_522_);
    return v___x_523_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2()
-> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_524_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1_once
        ),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__1,
    );
    v___x_525_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0_once
        ),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_526_ = l_Rat_div(v___x_525_, v___x_524_);
    return v___x_526_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3()
-> *mut LeanObject {
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    v___x_527_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2_once
        ),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__2,
    );
    v___x_528_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_527_);
    return v___x_528_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1() -> *mut LeanObject {
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    v___x_529_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3),
        core::ptr::addr_of_mut!(
            l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3_once
        ),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1___closed__3,
    );
    return v___x_529_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__0() -> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    v___x_530_ = lean_unsigned_to_nat(1);
    v___x_531_ =
        l_Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0(v___x_530_);
    return v___x_531_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__1() -> *mut LeanObject {
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___x_532_ = lean_unsigned_to_nat(1000000000);
    v___x_533_ =
        l_Nat_cast___at___00Std_Time_Nanosecond_instDecidableEqOffset___aux__1_spec__0(v___x_532_);
    return v___x_533_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2() -> *mut LeanObject {
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    v___x_534_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__1,
    );
    v___x_535_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__0,
    );
    v___x_536_ = l_Rat_div(v___x_535_, v___x_534_);
    return v___x_536_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__3() -> *mut LeanObject {
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    v___x_537_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__2_once),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__2,
    );
    v___x_538_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_537_);
    return v___x_538_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedOffset() -> *mut LeanObject {
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v___x_539_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instInhabitedOffset___closed__3_once),
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___closed__3,
    );
    return v___x_539_;
}
pub unsafe fn l_Std_Time_Nanosecond_instAddOffset___aux__1(
    mut v_u1_540_: *mut LeanObject,
    mut v_u2_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    v___x_542_ = lean_int_add(v_u1_540_, v_u2_541_);
    return v___x_542_;
}
pub unsafe fn l_Std_Time_Nanosecond_instAddOffset___aux__1___boxed(
    mut v_u1_543_: *mut LeanObject,
    mut v_u2_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_545_: *mut LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Std_Time_Nanosecond_instAddOffset___aux__1(v_u1_543_, v_u2_544_);
    lean_dec(v_u2_544_);
    lean_dec(v_u1_543_);
    return v_res_545_;
}
pub unsafe fn l_Std_Time_Nanosecond_instSubOffset___aux__1(
    mut v_u1_548_: *mut LeanObject,
    mut v_u2_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    v___x_550_ = lean_int_sub(v_u1_548_, v_u2_549_);
    return v___x_550_;
}
pub unsafe fn l_Std_Time_Nanosecond_instSubOffset___aux__1___boxed(
    mut v_u1_551_: *mut LeanObject,
    mut v_u2_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_553_: *mut LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Std_Time_Nanosecond_instSubOffset___aux__1(v_u1_551_, v_u2_552_);
    lean_dec(v_u2_552_);
    lean_dec(v_u1_551_);
    return v_res_553_;
}
pub unsafe fn l_Std_Time_Nanosecond_instNegOffset___aux__1(
    mut v_x_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    v___x_557_ = lean_int_neg(v_x_556_);
    return v___x_557_;
}
pub unsafe fn l_Std_Time_Nanosecond_instNegOffset___aux__1___boxed(
    mut v_x_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_559_: *mut LeanObject = core::ptr::null_mut();
    v_res_559_ = l_Std_Time_Nanosecond_instNegOffset___aux__1(v_x_558_);
    lean_dec(v_x_558_);
    return v_res_559_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instLEOffset() -> *mut LeanObject {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    v___x_562_ = lean_box(0);
    return v___x_562_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instLTOffset() -> *mut LeanObject {
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v___x_563_ = lean_box(0);
    return v___x_563_;
}
pub unsafe fn l_Std_Time_Nanosecond_instToStringOffset___aux__1(
    mut v_n_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = l_Int_repr(v_n_564_);
    return v___x_565_;
}
pub unsafe fn l_Std_Time_Nanosecond_instToStringOffset___aux__1___boxed(
    mut v_n_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_567_: *mut LeanObject = core::ptr::null_mut();
    v_res_567_ = l_Std_Time_Nanosecond_instToStringOffset___aux__1(v_n_566_);
    lean_dec(v_n_566_);
    return v_res_567_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(
    mut v_x_570_: *mut LeanObject,
    mut v_y_571_: *mut LeanObject,
) -> u8 {
    let mut v___x_572_: u8 = 0;
    v___x_572_ = lean_int_dec_le(v_x_570_, v_y_571_);
    return v___x_572_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1___boxed(
    mut v_x_573_: *mut LeanObject,
    mut v_y_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_575_: u8 = 0;
    let mut v_r_576_: *mut LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Std_Time_Nanosecond_instDecidableLeOffset___aux__1(v_x_573_, v_y_574_);
    lean_dec(v_y_574_);
    lean_dec(v_x_573_);
    v_r_576_ = lean_box((v_res_575_) as usize);
    return v_r_576_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOffset(
    mut v___y_577_: *mut LeanObject,
    mut v___y_578_: *mut LeanObject,
) -> u8 {
    let mut v___x_579_: u8 = 0;
    v___x_579_ = lean_int_dec_le(v___y_577_, v___y_578_);
    return v___x_579_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeOffset___boxed(
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_582_: u8 = 0;
    let mut v_r_583_: *mut LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Std_Time_Nanosecond_instDecidableLeOffset(v___y_580_, v___y_581_);
    lean_dec(v___y_581_);
    lean_dec(v___y_580_);
    v_r_583_ = lean_box((v_res_582_) as usize);
    return v_r_583_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(
    mut v_x_584_: *mut LeanObject,
    mut v_y_585_: *mut LeanObject,
) -> u8 {
    let mut v___x_586_: u8 = 0;
    v___x_586_ = lean_int_dec_lt(v_x_584_, v_y_585_);
    return v___x_586_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1___boxed(
    mut v_x_587_: *mut LeanObject,
    mut v_y_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_589_: u8 = 0;
    let mut v_r_590_: *mut LeanObject = core::ptr::null_mut();
    v_res_589_ = l_Std_Time_Nanosecond_instDecidableLtOffset___aux__1(v_x_587_, v_y_588_);
    lean_dec(v_y_588_);
    lean_dec(v_x_587_);
    v_r_590_ = lean_box((v_res_589_) as usize);
    return v_r_590_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOffset(
    mut v___y_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
) -> u8 {
    let mut v___x_593_: u8 = 0;
    v___x_593_ = lean_int_dec_lt(v___y_591_, v___y_592_);
    return v___x_593_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtOffset___boxed(
    mut v___y_594_: *mut LeanObject,
    mut v___y_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_596_: u8 = 0;
    let mut v_r_597_: *mut LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Std_Time_Nanosecond_instDecidableLtOffset(v___y_594_, v___y_595_);
    lean_dec(v___y_595_);
    lean_dec(v___y_594_);
    v_r_597_ = lean_box((v_res_596_) as usize);
    return v_r_597_;
}
pub unsafe fn l_Std_Time_Nanosecond_instOfNatOffset(
    mut v_n_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_599_ = lean_nat_to_int(v_n_598_);
    return v___x_599_;
}
pub unsafe fn l_Std_Time_Nanosecond_instOrdOffset___aux__1(
    mut v_x_600_: *mut LeanObject,
    mut v_y_601_: *mut LeanObject,
) -> u8 {
    let mut v___x_602_: u8 = 0;
    v___x_602_ = lean_int_dec_lt(v_x_600_, v_y_601_);
    if v___x_602_ == 0 {
        let mut v___x_603_: u8 = 0;
        v___x_603_ = lean_int_dec_eq(v_x_600_, v_y_601_);
        if v___x_603_ == 0 {
            let mut v___x_604_: u8 = 0;
            v___x_604_ = 2;
            return v___x_604_;
        } else {
            let mut v___x_605_: u8 = 0;
            v___x_605_ = 1;
            return v___x_605_;
        }
    } else {
        let mut v___x_606_: u8 = 0;
        v___x_606_ = 0;
        return v___x_606_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instOrdOffset___aux__1___boxed(
    mut v_x_607_: *mut LeanObject,
    mut v_y_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_609_: u8 = 0;
    let mut v_r_610_: *mut LeanObject = core::ptr::null_mut();
    v_res_609_ = l_Std_Time_Nanosecond_instOrdOffset___aux__1(v_x_607_, v_y_608_);
    lean_dec(v_y_608_);
    lean_dec(v_x_607_);
    v_r_610_ = lean_box((v_res_609_) as usize);
    return v_r_610_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofNat(
    mut v_data_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_nat_to_int(v_data_613_);
    return v___x_614_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofInt(
    mut v_data_615_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_615_);
    return v_data_615_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofInt___boxed(
    mut v_data_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_617_: *mut LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Std_Time_Nanosecond_Offset_ofInt(v_data_616_);
    lean_dec(v_data_616_);
    return v_res_617_;
}
pub unsafe fn l_Std_Time_Nanosecond_instReprSpan___aux__1(
    mut v_n_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    v___x_620_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_621_ = lean_int_dec_lt(v_n_618_, v___x_620_);
    if v___x_621_ == 0 {
        let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
        v___x_622_ = l_Int_repr(v_n_618_);
        v___x_623_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_623_, 0, v___x_622_);
        return v___x_623_;
    } else {
        let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
        v___x_624_ = l_Int_repr(v_n_618_);
        v___x_625_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_625_, 0, v___x_624_);
        v___x_626_ = l_Repr_addAppParen(v___x_625_, v_a_619_);
        return v___x_626_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instReprSpan___aux__1___boxed(
    mut v_n_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_629_: *mut LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Std_Time_Nanosecond_instReprSpan___aux__1(v_n_627_, v_a_628_);
    lean_dec(v_a_628_);
    lean_dec(v_n_627_);
    return v_res_629_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(
    mut v_a_631_: *mut LeanObject,
    mut v_b_632_: *mut LeanObject,
) -> u8 {
    let mut v___x_633_: u8 = 0;
    v___x_633_ = lean_int_dec_eq(v_a_631_, v_b_632_);
    return v___x_633_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1___boxed(
    mut v_a_634_: *mut LeanObject,
    mut v_b_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_636_: u8 = 0;
    let mut v_r_637_: *mut LeanObject = core::ptr::null_mut();
    v_res_636_ = l_Std_Time_Nanosecond_instDecidableEqSpan___aux__1(v_a_634_, v_b_635_);
    lean_dec(v_b_635_);
    lean_dec(v_a_634_);
    v_r_637_ = lean_box((v_res_636_) as usize);
    return v_r_637_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqSpan(
    mut v_a_638_: *mut LeanObject,
    mut v_b_639_: *mut LeanObject,
) -> u8 {
    let mut v___x_640_: u8 = 0;
    v___x_640_ = lean_int_dec_eq(v_a_638_, v_b_639_);
    return v___x_640_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableEqSpan___boxed(
    mut v_a_641_: *mut LeanObject,
    mut v_b_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Std_Time_Nanosecond_instDecidableEqSpan(v_a_641_, v_b_642_);
    lean_dec(v_b_642_);
    lean_dec(v_a_641_);
    v_r_644_ = lean_box((v_res_643_) as usize);
    return v_r_644_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instLESpan() -> *mut LeanObject {
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    v___x_645_ = lean_box(0);
    return v___x_645_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instLTSpan() -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___x_646_ = lean_box(0);
    return v___x_646_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_instInhabitedSpan() -> *mut LeanObject {
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    v___x_647_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    return v___x_647_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(
    mut v_x_648_: *mut LeanObject,
    mut v_y_649_: *mut LeanObject,
) -> u8 {
    let mut v___x_650_: u8 = 0;
    v___x_650_ = lean_int_dec_le(v_x_648_, v_y_649_);
    return v___x_650_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1___boxed(
    mut v_x_651_: *mut LeanObject,
    mut v_y_652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_653_: u8 = 0;
    let mut v_r_654_: *mut LeanObject = core::ptr::null_mut();
    v_res_653_ = l_Std_Time_Nanosecond_instDecidableLeSpan___aux__1(v_x_651_, v_y_652_);
    lean_dec(v_y_652_);
    lean_dec(v_x_651_);
    v_r_654_ = lean_box((v_res_653_) as usize);
    return v_r_654_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeSpan(
    mut v___y_655_: *mut LeanObject,
    mut v___y_656_: *mut LeanObject,
) -> u8 {
    let mut v___x_657_: u8 = 0;
    v___x_657_ = lean_int_dec_le(v___y_655_, v___y_656_);
    return v___x_657_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLeSpan___boxed(
    mut v___y_658_: *mut LeanObject,
    mut v___y_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_660_: u8 = 0;
    let mut v_r_661_: *mut LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Std_Time_Nanosecond_instDecidableLeSpan(v___y_658_, v___y_659_);
    lean_dec(v___y_659_);
    lean_dec(v___y_658_);
    v_r_661_ = lean_box((v_res_660_) as usize);
    return v_r_661_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(
    mut v_x_662_: *mut LeanObject,
    mut v_y_663_: *mut LeanObject,
) -> u8 {
    let mut v___x_664_: u8 = 0;
    v___x_664_ = lean_int_dec_lt(v_x_662_, v_y_663_);
    return v___x_664_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1___boxed(
    mut v_x_665_: *mut LeanObject,
    mut v_y_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_667_: u8 = 0;
    let mut v_r_668_: *mut LeanObject = core::ptr::null_mut();
    v_res_667_ = l_Std_Time_Nanosecond_instDecidableLtSpan___aux__1(v_x_665_, v_y_666_);
    lean_dec(v_y_666_);
    lean_dec(v_x_665_);
    v_r_668_ = lean_box((v_res_667_) as usize);
    return v_r_668_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtSpan(
    mut v___y_669_: *mut LeanObject,
    mut v___y_670_: *mut LeanObject,
) -> u8 {
    let mut v___x_671_: u8 = 0;
    v___x_671_ = lean_int_dec_lt(v___y_669_, v___y_670_);
    return v___x_671_;
}
pub unsafe fn l_Std_Time_Nanosecond_instDecidableLtSpan___boxed(
    mut v___y_672_: *mut LeanObject,
    mut v___y_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_674_: u8 = 0;
    let mut v_r_675_: *mut LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Std_Time_Nanosecond_instDecidableLtSpan(v___y_672_, v___y_673_);
    lean_dec(v___y_673_);
    lean_dec(v___y_672_);
    v_r_675_ = lean_box((v_res_674_) as usize);
    return v_r_675_;
}
pub unsafe fn l_Std_Time_Nanosecond_instOrdSpan___aux__1(
    mut v_x_676_: *mut LeanObject,
    mut v_y_677_: *mut LeanObject,
) -> u8 {
    let mut v___x_678_: u8 = 0;
    v___x_678_ = lean_int_dec_lt(v_x_676_, v_y_677_);
    if v___x_678_ == 0 {
        let mut v___x_679_: u8 = 0;
        v___x_679_ = lean_int_dec_eq(v_x_676_, v_y_677_);
        if v___x_679_ == 0 {
            let mut v___x_680_: u8 = 0;
            v___x_680_ = 2;
            return v___x_680_;
        } else {
            let mut v___x_681_: u8 = 0;
            v___x_681_ = 1;
            return v___x_681_;
        }
    } else {
        let mut v___x_682_: u8 = 0;
        v___x_682_ = 0;
        return v___x_682_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed(
    mut v_x_683_: *mut LeanObject,
    mut v_y_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_685_: u8 = 0;
    let mut v_r_686_: *mut LeanObject = core::ptr::null_mut();
    v_res_685_ = l_Std_Time_Nanosecond_instOrdSpan___aux__1(v_x_683_, v_y_684_);
    lean_dec(v_y_684_);
    lean_dec(v_x_683_);
    v_r_686_ = lean_box((v_res_685_) as usize);
    return v_r_686_;
}
pub unsafe fn l_Std_Time_Nanosecond_Span_toOffset(
    mut v_span_689_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_span_689_);
    return v_span_689_;
}
pub unsafe fn l_Std_Time_Nanosecond_Span_toOffset___boxed(
    mut v_span_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_691_: *mut LeanObject = core::ptr::null_mut();
    v_res_691_ = l_Std_Time_Nanosecond_Span_toOffset(v_span_690_);
    lean_dec(v_span_690_);
    return v_res_691_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(
    mut v_n_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    v___x_694_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_695_ = lean_int_dec_lt(v_n_692_, v___x_694_);
    if v___x_695_ == 0 {
        let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        v___x_696_ = l_Int_repr(v_n_692_);
        v___x_697_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_697_, 0, v___x_696_);
        return v___x_697_;
    } else {
        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
        v___x_698_ = l_Int_repr(v_n_692_);
        v___x_699_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_699_, 0, v___x_698_);
        v___x_700_ = l_Repr_addAppParen(v___x_699_, v_a_693_);
        return v___x_700_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1___boxed(
    mut v_n_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Std_Time_Nanosecond_Ordinal_instReprOfDay___aux__1(v_n_701_, v_a_702_);
    lean_dec(v_a_702_);
    lean_dec(v_n_701_);
    return v_res_703_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(
    mut v_a_705_: *mut LeanObject,
    mut v_b_706_: *mut LeanObject,
) -> u8 {
    let mut v___x_707_: u8 = 0;
    v___x_707_ = lean_int_dec_eq(v_a_705_, v_b_706_);
    return v___x_707_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1___boxed(
    mut v_a_708_: *mut LeanObject,
    mut v_b_709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_710_: u8 = 0;
    let mut v_r_711_: *mut LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___aux__1(v_a_708_, v_b_709_);
    lean_dec(v_b_709_);
    lean_dec(v_a_708_);
    v_r_711_ = lean_box((v_res_710_) as usize);
    return v_r_711_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(
    mut v_a_712_: *mut LeanObject,
    mut v_b_713_: *mut LeanObject,
) -> u8 {
    let mut v___x_714_: u8 = 0;
    v___x_714_ = lean_int_dec_eq(v_a_712_, v_b_713_);
    return v___x_714_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay___boxed(
    mut v_a_715_: *mut LeanObject,
    mut v_b_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_717_: u8 = 0;
    let mut v_r_718_: *mut LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Std_Time_Nanosecond_Ordinal_instDecidableEqOfDay(v_a_715_, v_b_716_);
    lean_dec(v_b_716_);
    lean_dec(v_a_715_);
    v_r_718_ = lean_box((v_res_717_) as usize);
    return v_r_718_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay() -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    v___x_719_ = lean_box(0);
    return v___x_719_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay() -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    v___x_720_ = lean_box(0);
    return v___x_720_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay() -> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Nanosecond_instReprOrdinal___aux__1___closed__0,
    );
    return v___x_721_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(
    mut v_x_722_: *mut LeanObject,
    mut v_y_723_: *mut LeanObject,
) -> u8 {
    let mut v___x_724_: u8 = 0;
    v___x_724_ = lean_int_dec_le(v_x_722_, v_y_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1___boxed(
    mut v_x_725_: *mut LeanObject,
    mut v_y_726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_727_: u8 = 0;
    let mut v_r_728_: *mut LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___aux__1(v_x_725_, v_y_726_);
    lean_dec(v_y_726_);
    lean_dec(v_x_725_);
    v_r_728_ = lean_box((v_res_727_) as usize);
    return v_r_728_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(
    mut v___y_729_: *mut LeanObject,
    mut v___y_730_: *mut LeanObject,
) -> u8 {
    let mut v___x_731_: u8 = 0;
    v___x_731_ = lean_int_dec_le(v___y_729_, v___y_730_);
    return v___x_731_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay___boxed(
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_734_: u8 = 0;
    let mut v_r_735_: *mut LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLeOfDay(v___y_732_, v___y_733_);
    lean_dec(v___y_733_);
    lean_dec(v___y_732_);
    v_r_735_ = lean_box((v_res_734_) as usize);
    return v_r_735_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(
    mut v_x_736_: *mut LeanObject,
    mut v_y_737_: *mut LeanObject,
) -> u8 {
    let mut v___x_738_: u8 = 0;
    v___x_738_ = lean_int_dec_lt(v_x_736_, v_y_737_);
    return v___x_738_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1___boxed(
    mut v_x_739_: *mut LeanObject,
    mut v_y_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_741_: u8 = 0;
    let mut v_r_742_: *mut LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___aux__1(v_x_739_, v_y_740_);
    lean_dec(v_y_740_);
    lean_dec(v_x_739_);
    v_r_742_ = lean_box((v_res_741_) as usize);
    return v_r_742_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
) -> u8 {
    let mut v___x_745_: u8 = 0;
    v___x_745_ = lean_int_dec_lt(v___y_743_, v___y_744_);
    return v___x_745_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay___boxed(
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_748_: u8 = 0;
    let mut v_r_749_: *mut LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Std_Time_Nanosecond_Ordinal_instDecidableLtOfDay(v___y_746_, v___y_747_);
    lean_dec(v___y_747_);
    lean_dec(v___y_746_);
    v_r_749_ = lean_box((v_res_748_) as usize);
    return v_r_749_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(
    mut v_x_750_: *mut LeanObject,
    mut v_y_751_: *mut LeanObject,
) -> u8 {
    let mut v___x_752_: u8 = 0;
    v___x_752_ = lean_int_dec_lt(v_x_750_, v_y_751_);
    if v___x_752_ == 0 {
        let mut v___x_753_: u8 = 0;
        v___x_753_ = lean_int_dec_eq(v_x_750_, v_y_751_);
        if v___x_753_ == 0 {
            let mut v___x_754_: u8 = 0;
            v___x_754_ = 2;
            return v___x_754_;
        } else {
            let mut v___x_755_: u8 = 0;
            v___x_755_ = 1;
            return v___x_755_;
        }
    } else {
        let mut v___x_756_: u8 = 0;
        v___x_756_ = 0;
        return v___x_756_;
    }
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1___boxed(
    mut v_x_757_: *mut LeanObject,
    mut v_y_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_759_: u8 = 0;
    let mut v_r_760_: *mut LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Std_Time_Nanosecond_Ordinal_instOrdOfDay___aux__1(v_x_757_, v_y_758_);
    lean_dec(v_y_758_);
    lean_dec(v_x_757_);
    v_r_760_ = lean_box((v_res_759_) as usize);
    return v_r_760_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(
    mut v_data_763_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_763_);
    return v_data_763_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofInt___redArg___boxed(
    mut v_data_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_765_: *mut LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Std_Time_Nanosecond_Ordinal_ofInt___redArg(v_data_764_);
    lean_dec(v_data_764_);
    return v_res_765_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofInt(
    mut v_data_766_: *mut LeanObject,
    mut v_h_767_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_766_);
    return v_data_766_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofInt___boxed(
    mut v_data_768_: *mut LeanObject,
    mut v_h_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_770_: *mut LeanObject = core::ptr::null_mut();
    v_res_770_ = l_Std_Time_Nanosecond_Ordinal_ofInt(v_data_768_, v_h_769_);
    lean_dec(v_data_768_);
    return v_res_770_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofNat___redArg(
    mut v_data_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = lean_nat_to_int(v_data_771_);
    return v___x_772_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofNat(
    mut v_data_773_: *mut LeanObject,
    mut v_h_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_775_ = lean_nat_to_int(v_data_773_);
    return v___x_775_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_ofFin(
    mut v_data_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ = lean_nat_to_int(v_data_776_);
    return v___x_777_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_toOffset(
    mut v_ordinal_778_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ordinal_778_);
    return v_ordinal_778_;
}
pub unsafe fn l_Std_Time_Nanosecond_Ordinal_toOffset___boxed(
    mut v_ordinal_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_780_: *mut LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Std_Time_Nanosecond_Ordinal_toOffset(v_ordinal_779_);
    lean_dec(v_ordinal_779_);
    return v_res_780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_Nanosecond_instLEOrdinal = _init_l_Std_Time_Nanosecond_instLEOrdinal();
    lean_mark_persistent(l_Std_Time_Nanosecond_instLEOrdinal);
    l_Std_Time_Nanosecond_instLTOrdinal = _init_l_Std_Time_Nanosecond_instLTOrdinal();
    lean_mark_persistent(l_Std_Time_Nanosecond_instLTOrdinal);
    l_Std_Time_Nanosecond_instInhabitedOrdinal = _init_l_Std_Time_Nanosecond_instInhabitedOrdinal();
    lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOrdinal);
    l_Std_Time_Nanosecond_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Nanosecond_instInhabitedOffset___aux__1();
    lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOffset___aux__1);
    l_Std_Time_Nanosecond_instInhabitedOffset = _init_l_Std_Time_Nanosecond_instInhabitedOffset();
    lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedOffset);
    l_Std_Time_Nanosecond_instLEOffset = _init_l_Std_Time_Nanosecond_instLEOffset();
    lean_mark_persistent(l_Std_Time_Nanosecond_instLEOffset);
    l_Std_Time_Nanosecond_instLTOffset = _init_l_Std_Time_Nanosecond_instLTOffset();
    lean_mark_persistent(l_Std_Time_Nanosecond_instLTOffset);
    l_Std_Time_Nanosecond_instLESpan = _init_l_Std_Time_Nanosecond_instLESpan();
    lean_mark_persistent(l_Std_Time_Nanosecond_instLESpan);
    l_Std_Time_Nanosecond_instLTSpan = _init_l_Std_Time_Nanosecond_instLTSpan();
    lean_mark_persistent(l_Std_Time_Nanosecond_instLTSpan);
    l_Std_Time_Nanosecond_instInhabitedSpan = _init_l_Std_Time_Nanosecond_instInhabitedSpan();
    lean_mark_persistent(l_Std_Time_Nanosecond_instInhabitedSpan);
    l_Std_Time_Nanosecond_Ordinal_instLEOfDay = _init_l_Std_Time_Nanosecond_Ordinal_instLEOfDay();
    lean_mark_persistent(l_Std_Time_Nanosecond_Ordinal_instLEOfDay);
    l_Std_Time_Nanosecond_Ordinal_instLTOfDay = _init_l_Std_Time_Nanosecond_Ordinal_instLTOfDay();
    lean_mark_persistent(l_Std_Time_Nanosecond_Ordinal_instLTOfDay);
    l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay =
        _init_l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay();
    lean_mark_persistent(l_Std_Time_Nanosecond_Ordinal_instInhabitedOfDay);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Nanosecond(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_Unit_Nanosecond(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Nanosecond(builtin);
}
