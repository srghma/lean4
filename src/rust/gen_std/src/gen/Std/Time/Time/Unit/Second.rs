// Lean compiler output
// Module: Std.Time.Time.Unit.Second
// Imports: Std.Time.Time.Unit.Nanosecond
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_emod, lean_int_neg,
    lean_int_sub, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_instNatCast___lam__0, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Internal::Bounded::l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast;
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::r#gen::Std::Time::Time::Unit::Nanosecond::{
    initialize_Std_Time_Time_Unit_Nanosecond, runtime_initialize_Std_Time_Time_Unit_Nanosecond,
};
static mut l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instReprOrdinal___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Second_instReprOrdinal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Second_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Second_instReprOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Second_instToStringOrdinal___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
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
static mut l_Std_Time_Second_instToStringOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instToStringOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Second_instOfNatOrdinal___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instOfNatOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_instOfNatOrdinal___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instOfNatOrdinal___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_instOfNatOrdinal___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instOfNatOrdinal___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_instOfNatOrdinal___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instOfNatOrdinal___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_instOfNatOrdinal___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instOfNatOrdinal___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Second_instReprOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Second_instReprOffset___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Second_instReprOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instReprOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Second_instReprOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instReprOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Second_instInhabitedOffset___aux__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_instInhabitedOffset___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instInhabitedOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_instInhabitedOffset___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_instInhabitedOffset___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Second_instInhabitedOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Second_instAddOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Second_instAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Second_instAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Second_instSubOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Second_instSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Second_instSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Second_instNegOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Second_instNegOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Second_instNegOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Second_instLEOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Second_instLTOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Second_instToStringOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instToStringOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Second_instOrdOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Second_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Second_instOrdOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Second_instOrdOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Second_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Time_Second_instLEOrdinal(
    mut v_leap_337_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = leanh::lean_box(0);
    return v___x_338_;
}
pub unsafe fn l_Std_Time_Second_instLEOrdinal___boxed(
    mut v_leap_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_340_: u8 = 0;
    let mut v_res_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_340_ = (leanh::lean_unbox(v_leap_339_) as u8);
    v_res_341_ = l_Std_Time_Second_instLEOrdinal(v_leap_boxed_340_);
    return v_res_341_;
}
pub unsafe fn l_Std_Time_Second_instLTOrdinal(
    mut v_leap_342_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = leanh::lean_box(0);
    return v___x_343_;
}
pub unsafe fn l_Std_Time_Second_instLTOrdinal___boxed(
    mut v_leap_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_345_: u8 = 0;
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_345_ = (leanh::lean_unbox(v_leap_344_) as u8);
    v_res_346_ = l_Std_Time_Second_instLTOrdinal(v_leap_boxed_345_);
    return v_res_346_;
}
pub unsafe fn _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = leanh::lean_unsigned_to_nat(0);
    v___x_348_ = lean_nat_to_int(v___x_347_);
    return v___x_348_;
}
pub unsafe fn l_Std_Time_Second_instReprOrdinal___lam__0(
    mut v_r_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: u8 = 0;
    v___x_351_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once),
        _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0,
    );
    v___x_352_ = lean_int_dec_lt(v_r_349_, v___x_351_);
    if v___x_352_ == 0 {
        let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_353_ = l_Int_repr(v_r_349_);
        v___x_354_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_354_, 0, v___x_353_);
        return v___x_354_;
    } else {
        let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_355_ = l_Int_repr(v_r_349_);
        v___x_356_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_356_, 0, v___x_355_);
        v___x_357_ = l_Repr_addAppParen(v___x_356_, v___y_350_);
        return v___x_357_;
    }
}
pub unsafe fn l_Std_Time_Second_instReprOrdinal___lam__0___boxed(
    mut v_r_358_: *mut leanh::LeanObject,
    mut v___y_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_Std_Time_Second_instReprOrdinal___lam__0(v_r_358_, v___y_359_);
    leanh::lean_dec(v___y_359_);
    leanh::lean_dec(v_r_358_);
    return v_res_360_;
}
pub unsafe fn l_Std_Time_Second_instReprOrdinal(
    mut v_leap_362_: u8,
) -> *mut leanh::LeanObject {
    let mut v___f_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_363_ = l_Std_Time_Second_instReprOrdinal___closed__0;
    return v___f_363_;
}
pub unsafe fn l_Std_Time_Second_instReprOrdinal___boxed(
    mut v_leap_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_365_: u8 = 0;
    let mut v_res_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_365_ = (leanh::lean_unbox(v_leap_364_) as u8);
    v_res_366_ = l_Std_Time_Second_instReprOrdinal(v_leap_boxed_365_);
    return v_res_366_;
}
pub unsafe fn l_Std_Time_Second_instToStringOrdinal(
    mut v_leap_368_: u8,
) -> *mut leanh::LeanObject {
    let mut v___f_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_369_ = l_Std_Time_Second_instToStringOrdinal___closed__0;
    return v___f_369_;
}
pub unsafe fn l_Std_Time_Second_instToStringOrdinal___boxed(
    mut v_leap_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_371_: u8 = 0;
    let mut v_res_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_371_ = (leanh::lean_unbox(v_leap_370_) as u8);
    v_res_372_ = l_Std_Time_Second_instToStringOrdinal(v_leap_boxed_371_);
    return v_res_372_;
}
pub unsafe fn _init_l_Std_Time_Second_instOfNatOrdinal___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_unsigned_to_nat(59);
    v___x_374_ = lean_nat_to_int(v___x_373_);
    return v___x_374_;
}
pub unsafe fn _init_l_Std_Time_Second_instOfNatOrdinal___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__0_once),
        _init_l_Std_Time_Second_instOfNatOrdinal___closed__0,
    );
    v___x_376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once),
        _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0,
    );
    v___x_377_ = lean_int_add(v___x_376_, v___x_375_);
    return v___x_377_;
}
pub unsafe fn _init_l_Std_Time_Second_instOfNatOrdinal___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once),
        _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0,
    );
    v___x_379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__1_once),
        _init_l_Std_Time_Second_instOfNatOrdinal___closed__1,
    );
    v___x_380_ = lean_int_sub(v___x_379_, v___x_378_);
    return v___x_380_;
}
pub unsafe fn _init_l_Std_Time_Second_instOfNatOrdinal___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = leanh::lean_unsigned_to_nat(1);
    v___x_382_ = lean_nat_to_int(v___x_381_);
    return v___x_382_;
}
pub unsafe fn _init_l_Std_Time_Second_instOfNatOrdinal___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__3_once),
        _init_l_Std_Time_Second_instOfNatOrdinal___closed__3,
    );
    v___x_384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__2_once),
        _init_l_Std_Time_Second_instOfNatOrdinal___closed__2,
    );
    v_range_385_ = lean_int_add(v___x_384_, v___x_383_);
    return v_range_385_;
}
pub unsafe fn l_Std_Time_Second_instOfNatOrdinal(
    mut v_leap_386_: u8,
    mut v_n_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once),
        _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0,
    );
    v___x_389_ = leanh::lean_unsigned_to_nat(59);
    if v_leap_386_ == 0 {
        let mut v_inst_390_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_inst_390_ =
            l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_388_, v_n_387_, v___x_389_);
        return v_inst_390_;
    } else {
        let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_range_392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_391_ = lean_nat_to_int(v_n_387_);
        v_range_392_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__4),
            core::ptr::addr_of_mut!(l_Std_Time_Second_instOfNatOrdinal___closed__4_once),
            _init_l_Std_Time_Second_instOfNatOrdinal___closed__4,
        );
        v___x_393_ = lean_int_sub(v___x_391_, v___x_388_);
        leanh::lean_dec(v___x_391_);
        v___x_394_ = lean_int_emod(v___x_393_, v_range_392_);
        leanh::lean_dec(v___x_393_);
        v___x_395_ = lean_int_add(v___x_394_, v_range_392_);
        leanh::lean_dec(v___x_394_);
        v___x_396_ = lean_int_emod(v___x_395_, v_range_392_);
        leanh::lean_dec(v___x_395_);
        v___x_397_ = lean_int_add(v___x_396_, v___x_388_);
        leanh::lean_dec(v___x_396_);
        return v___x_397_;
    }
}
pub unsafe fn l_Std_Time_Second_instOfNatOrdinal___boxed(
    mut v_leap_398_: *mut leanh::LeanObject,
    mut v_n_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_400_: u8 = 0;
    let mut v_res_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_400_ = (leanh::lean_unbox(v_leap_398_) as u8);
    v_res_401_ = l_Std_Time_Second_instOfNatOrdinal(v_leap_boxed_400_, v_n_399_);
    return v_res_401_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOrdinal___redArg(
    mut v_x_402_: *mut leanh::LeanObject,
    mut v_y_403_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_404_: u8 = 0;
    v___x_404_ = lean_int_dec_le(v_x_402_, v_y_403_);
    return v___x_404_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOrdinal___redArg___boxed(
    mut v_x_405_: *mut leanh::LeanObject,
    mut v_y_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_407_: u8 = 0;
    let mut v_r_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_407_ = l_Std_Time_Second_instDecidableLeOrdinal___redArg(v_x_405_, v_y_406_);
    leanh::lean_dec(v_y_406_);
    leanh::lean_dec(v_x_405_);
    v_r_408_ = leanh::lean_box((v_res_407_) as usize);
    return v_r_408_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOrdinal(
    mut v_leap_409_: u8,
    mut v_x_410_: *mut leanh::LeanObject,
    mut v_y_411_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_412_: u8 = 0;
    v___x_412_ = lean_int_dec_le(v_x_410_, v_y_411_);
    return v___x_412_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOrdinal___boxed(
    mut v_leap_413_: *mut leanh::LeanObject,
    mut v_x_414_: *mut leanh::LeanObject,
    mut v_y_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_416_: u8 = 0;
    let mut v_res_417_: u8 = 0;
    let mut v_r_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_416_ = (leanh::lean_unbox(v_leap_413_) as u8);
    v_res_417_ = l_Std_Time_Second_instDecidableLeOrdinal(v_leap_boxed_416_, v_x_414_, v_y_415_);
    leanh::lean_dec(v_y_415_);
    leanh::lean_dec(v_x_414_);
    v_r_418_ = leanh::lean_box((v_res_417_) as usize);
    return v_r_418_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOrdinal___redArg(
    mut v_x_419_: *mut leanh::LeanObject,
    mut v_y_420_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_421_: u8 = 0;
    v___x_421_ = lean_int_dec_lt(v_x_419_, v_y_420_);
    return v___x_421_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOrdinal___redArg___boxed(
    mut v_x_422_: *mut leanh::LeanObject,
    mut v_y_423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_424_: u8 = 0;
    let mut v_r_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Std_Time_Second_instDecidableLtOrdinal___redArg(v_x_422_, v_y_423_);
    leanh::lean_dec(v_y_423_);
    leanh::lean_dec(v_x_422_);
    v_r_425_ = leanh::lean_box((v_res_424_) as usize);
    return v_r_425_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOrdinal(
    mut v_leap_426_: u8,
    mut v_x_427_: *mut leanh::LeanObject,
    mut v_y_428_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_429_: u8 = 0;
    v___x_429_ = lean_int_dec_lt(v_x_427_, v_y_428_);
    return v___x_429_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOrdinal___boxed(
    mut v_leap_430_: *mut leanh::LeanObject,
    mut v_x_431_: *mut leanh::LeanObject,
    mut v_y_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_433_: u8 = 0;
    let mut v_res_434_: u8 = 0;
    let mut v_r_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_433_ = (leanh::lean_unbox(v_leap_430_) as u8);
    v_res_434_ = l_Std_Time_Second_instDecidableLtOrdinal(v_leap_boxed_433_, v_x_431_, v_y_432_);
    leanh::lean_dec(v_y_432_);
    leanh::lean_dec(v_x_431_);
    v_r_435_ = leanh::lean_box((v_res_434_) as usize);
    return v_r_435_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_b_437_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_438_: u8 = 0;
    v___x_438_ = lean_int_dec_eq(v_a_436_, v_b_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg___boxed(
    mut v_a_439_: *mut leanh::LeanObject,
    mut v_b_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_441_: u8 = 0;
    let mut v_r_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_441_ = l_Std_Time_Second_instDecidableEqOrdinal___aux__1___redArg(v_a_439_, v_b_440_);
    leanh::lean_dec(v_b_440_);
    leanh::lean_dec(v_a_439_);
    v_r_442_ = leanh::lean_box((v_res_441_) as usize);
    return v_r_442_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___aux__1(
    mut v_leap_443_: u8,
    mut v_a_444_: *mut leanh::LeanObject,
    mut v_b_445_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_446_: u8 = 0;
    v___x_446_ = lean_int_dec_eq(v_a_444_, v_b_445_);
    return v___x_446_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___aux__1___boxed(
    mut v_leap_447_: *mut leanh::LeanObject,
    mut v_a_448_: *mut leanh::LeanObject,
    mut v_b_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_450_: u8 = 0;
    let mut v_res_451_: u8 = 0;
    let mut v_r_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_450_ = (leanh::lean_unbox(v_leap_447_) as u8);
    v_res_451_ =
        l_Std_Time_Second_instDecidableEqOrdinal___aux__1(v_leap_boxed_450_, v_a_448_, v_b_449_);
    leanh::lean_dec(v_b_449_);
    leanh::lean_dec(v_a_448_);
    v_r_452_ = leanh::lean_box((v_res_451_) as usize);
    return v_r_452_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___redArg(
    mut v_a_453_: *mut leanh::LeanObject,
    mut v_b_454_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_455_: u8 = 0;
    v___x_455_ = lean_int_dec_eq(v_a_453_, v_b_454_);
    return v___x_455_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___redArg___boxed(
    mut v_a_456_: *mut leanh::LeanObject,
    mut v_b_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_458_: u8 = 0;
    let mut v_r_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_458_ = l_Std_Time_Second_instDecidableEqOrdinal___redArg(v_a_456_, v_b_457_);
    leanh::lean_dec(v_b_457_);
    leanh::lean_dec(v_a_456_);
    v_r_459_ = leanh::lean_box((v_res_458_) as usize);
    return v_r_459_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal(
    mut v_leap_460_: u8,
    mut v_a_461_: *mut leanh::LeanObject,
    mut v_b_462_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_463_: u8 = 0;
    v___x_463_ = lean_int_dec_eq(v_a_461_, v_b_462_);
    return v___x_463_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOrdinal___boxed(
    mut v_leap_464_: *mut leanh::LeanObject,
    mut v_a_465_: *mut leanh::LeanObject,
    mut v_b_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_467_: u8 = 0;
    let mut v_res_468_: u8 = 0;
    let mut v_r_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_467_ = (leanh::lean_unbox(v_leap_464_) as u8);
    v_res_468_ = l_Std_Time_Second_instDecidableEqOrdinal(v_leap_boxed_467_, v_a_465_, v_b_466_);
    leanh::lean_dec(v_b_466_);
    leanh::lean_dec(v_a_465_);
    v_r_469_ = leanh::lean_box((v_res_468_) as usize);
    return v_r_469_;
}
pub unsafe fn l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(
    mut v_x_470_: *mut leanh::LeanObject,
    mut v_y_471_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_472_: u8 = 0;
    v___x_472_ = lean_int_dec_lt(v_x_470_, v_y_471_);
    if v___x_472_ == 0 {
        let mut v___x_473_: u8 = 0;
        v___x_473_ = lean_int_dec_eq(v_x_470_, v_y_471_);
        if v___x_473_ == 0 {
            let mut v___x_474_: u8 = 0;
            v___x_474_ = 2;
            return v___x_474_;
        } else {
            let mut v___x_475_: u8 = 0;
            v___x_475_ = 1;
            return v___x_475_;
        }
    } else {
        let mut v___x_476_: u8 = 0;
        v___x_476_ = 0;
        return v___x_476_;
    }
}
pub unsafe fn l_Std_Time_Second_instOrdOrdinal___aux__1___redArg___boxed(
    mut v_x_477_: *mut leanh::LeanObject,
    mut v_y_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_479_: u8 = 0;
    let mut v_r_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Std_Time_Second_instOrdOrdinal___aux__1___redArg(v_x_477_, v_y_478_);
    leanh::lean_dec(v_y_478_);
    leanh::lean_dec(v_x_477_);
    v_r_480_ = leanh::lean_box((v_res_479_) as usize);
    return v_r_480_;
}
pub unsafe fn l_Std_Time_Second_instOrdOrdinal___aux__1(
    mut v_leap_481_: u8,
    mut v_x_482_: *mut leanh::LeanObject,
    mut v_y_483_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_484_: u8 = 0;
    v___x_484_ = lean_int_dec_lt(v_x_482_, v_y_483_);
    if v___x_484_ == 0 {
        let mut v___x_485_: u8 = 0;
        v___x_485_ = lean_int_dec_eq(v_x_482_, v_y_483_);
        if v___x_485_ == 0 {
            let mut v___x_486_: u8 = 0;
            v___x_486_ = 2;
            return v___x_486_;
        } else {
            let mut v___x_487_: u8 = 0;
            v___x_487_ = 1;
            return v___x_487_;
        }
    } else {
        let mut v___x_488_: u8 = 0;
        v___x_488_ = 0;
        return v___x_488_;
    }
}
pub unsafe fn l_Std_Time_Second_instOrdOrdinal___aux__1___boxed(
    mut v_leap_489_: *mut leanh::LeanObject,
    mut v_x_490_: *mut leanh::LeanObject,
    mut v_y_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_492_: u8 = 0;
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_492_ = (leanh::lean_unbox(v_leap_489_) as u8);
    v_res_493_ = l_Std_Time_Second_instOrdOrdinal___aux__1(v_leap_boxed_492_, v_x_490_, v_y_491_);
    leanh::lean_dec(v_y_491_);
    leanh::lean_dec(v_x_490_);
    v_r_494_ = leanh::lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn l_Std_Time_Second_instOrdOrdinal(
    mut v_leap_495_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = leanh::lean_box((v_leap_495_) as usize);
    v___x_497_ = leanh::lean_alloc_closure(
        l_Std_Time_Second_instOrdOrdinal___aux__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_497_, 0, v___x_496_);
    return v___x_497_;
}
pub unsafe fn l_Std_Time_Second_instOrdOrdinal___boxed(
    mut v_leap_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_499_: u8 = 0;
    let mut v_res_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_499_ = (leanh::lean_unbox(v_leap_498_) as u8);
    v_res_500_ = l_Std_Time_Second_instOrdOrdinal(v_leap_boxed_499_);
    return v_res_500_;
}
pub unsafe fn l_Std_Time_Second_instReprOffset___aux__1(
    mut v_x_501_: *mut leanh::LeanObject,
    mut v_p_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: u8 = 0;
    v___x_503_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once),
        _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0,
    );
    v___x_504_ = lean_int_dec_lt(v_x_501_, v___x_503_);
    if v___x_504_ == 0 {
        let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_505_ = l_Int_repr(v_x_501_);
        v___x_506_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_506_, 0, v___x_505_);
        return v___x_506_;
    } else {
        let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_507_ = l_Int_repr(v_x_501_);
        v___x_508_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_508_, 0, v___x_507_);
        v___x_509_ = l_Repr_addAppParen(v___x_508_, v_p_502_);
        return v___x_509_;
    }
}
pub unsafe fn l_Std_Time_Second_instReprOffset___aux__1___boxed(
    mut v_x_510_: *mut leanh::LeanObject,
    mut v_p_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_512_ = l_Std_Time_Second_instReprOffset___aux__1(v_x_510_, v_p_511_);
    leanh::lean_dec(v_p_511_);
    leanh::lean_dec(v_x_510_);
    return v_res_512_;
}
pub unsafe fn l_Std_Time_Second_instReprOffset___lam__0(
    mut v___y_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    v___x_515_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instReprOrdinal___lam__0___closed__0_once),
        _init_l_Std_Time_Second_instReprOrdinal___lam__0___closed__0,
    );
    v___x_516_ = lean_int_dec_lt(v___y_513_, v___x_515_);
    if v___x_516_ == 0 {
        let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_517_ = l_Int_repr(v___y_513_);
        v___x_518_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_518_, 0, v___x_517_);
        return v___x_518_;
    } else {
        let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_519_ = l_Int_repr(v___y_513_);
        v___x_520_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_520_, 0, v___x_519_);
        v___x_521_ = l_Repr_addAppParen(v___x_520_, v___y_514_);
        return v___x_521_;
    }
}
pub unsafe fn l_Std_Time_Second_instReprOffset___lam__0___boxed(
    mut v___y_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_Time_Second_instReprOffset___lam__0(v___y_522_, v___y_523_);
    leanh::lean_dec(v___y_523_);
    leanh::lean_dec(v___y_522_);
    return v_res_524_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOffset___aux__1(
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_b_528_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_529_: u8 = 0;
    v___x_529_ = lean_int_dec_eq(v_a_527_, v_b_528_);
    return v___x_529_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOffset___aux__1___boxed(
    mut v_a_530_: *mut leanh::LeanObject,
    mut v_b_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_532_: u8 = 0;
    let mut v_r_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Std_Time_Second_instDecidableEqOffset___aux__1(v_a_530_, v_b_531_);
    leanh::lean_dec(v_b_531_);
    leanh::lean_dec(v_a_530_);
    v_r_533_ = leanh::lean_box((v_res_532_) as usize);
    return v_r_533_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Second_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ = lean_nat_to_int(v_a_534_);
    return v___x_535_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Second_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = lean_nat_to_int(v_a_536_);
    v___x_538_ = l_Rat_ofInt(v___x_537_);
    return v___x_538_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOffset(
    mut v_a_539_: *mut leanh::LeanObject,
    mut v_b_540_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_541_: u8 = 0;
    v___x_541_ = lean_int_dec_eq(v_a_539_, v_b_540_);
    return v___x_541_;
}
pub unsafe fn l_Std_Time_Second_instDecidableEqOffset___boxed(
    mut v_a_542_: *mut leanh::LeanObject,
    mut v_b_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_544_: u8 = 0;
    let mut v_r_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_544_ = l_Std_Time_Second_instDecidableEqOffset(v_a_542_, v_b_543_);
    leanh::lean_dec(v_b_543_);
    leanh::lean_dec(v_a_542_);
    v_r_545_ = leanh::lean_box((v_res_544_) as usize);
    return v_r_545_;
}
pub unsafe fn _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = leanh::lean_unsigned_to_nat(1);
    v___x_547_ = l_Rat_instNatCast___lam__0(v___x_546_);
    return v___x_547_;
}
pub unsafe fn _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_549_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_548_);
    return v___x_549_;
}
pub unsafe fn _init_l_Std_Time_Second_instInhabitedOffset___aux__1() -> *mut leanh::LeanObject
{
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Second_instInhabitedOffset___aux__1___closed__1,
    );
    return v___x_550_;
}
pub unsafe fn _init_l_Std_Time_Second_instInhabitedOffset___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = leanh::lean_unsigned_to_nat(1);
    v___x_552_ =
        l_Nat_cast___at___00Std_Time_Second_instDecidableEqOffset___aux__1_spec__0(v___x_551_);
    return v___x_552_;
}
pub unsafe fn _init_l_Std_Time_Second_instInhabitedOffset___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Second_instInhabitedOffset___closed__0,
    );
    v___x_554_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_553_);
    return v___x_554_;
}
pub unsafe fn _init_l_Std_Time_Second_instInhabitedOffset() -> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Second_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Second_instInhabitedOffset___closed__1,
    );
    return v___x_555_;
}
pub unsafe fn l_Std_Time_Second_instAddOffset___aux__1(
    mut v_u1_556_: *mut leanh::LeanObject,
    mut v_u2_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = lean_int_add(v_u1_556_, v_u2_557_);
    return v___x_558_;
}
pub unsafe fn l_Std_Time_Second_instAddOffset___aux__1___boxed(
    mut v_u1_559_: *mut leanh::LeanObject,
    mut v_u2_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_561_ = l_Std_Time_Second_instAddOffset___aux__1(v_u1_559_, v_u2_560_);
    leanh::lean_dec(v_u2_560_);
    leanh::lean_dec(v_u1_559_);
    return v_res_561_;
}
pub unsafe fn l_Std_Time_Second_instSubOffset___aux__1(
    mut v_u1_564_: *mut leanh::LeanObject,
    mut v_u2_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = lean_int_sub(v_u1_564_, v_u2_565_);
    return v___x_566_;
}
pub unsafe fn l_Std_Time_Second_instSubOffset___aux__1___boxed(
    mut v_u1_567_: *mut leanh::LeanObject,
    mut v_u2_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_569_ = l_Std_Time_Second_instSubOffset___aux__1(v_u1_567_, v_u2_568_);
    leanh::lean_dec(v_u2_568_);
    leanh::lean_dec(v_u1_567_);
    return v_res_569_;
}
pub unsafe fn l_Std_Time_Second_instNegOffset___aux__1(
    mut v_x_572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = lean_int_neg(v_x_572_);
    return v___x_573_;
}
pub unsafe fn l_Std_Time_Second_instNegOffset___aux__1___boxed(
    mut v_x_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Std_Time_Second_instNegOffset___aux__1(v_x_574_);
    leanh::lean_dec(v_x_574_);
    return v_res_575_;
}
pub unsafe fn _init_l_Std_Time_Second_instLEOffset() -> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = leanh::lean_box(0);
    return v___x_578_;
}
pub unsafe fn _init_l_Std_Time_Second_instLTOffset() -> *mut leanh::LeanObject {
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = leanh::lean_box(0);
    return v___x_579_;
}
pub unsafe fn l_Std_Time_Second_instToStringOffset___aux__1(
    mut v_n_580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = l_Int_repr(v_n_580_);
    return v___x_581_;
}
pub unsafe fn l_Std_Time_Second_instToStringOffset___aux__1___boxed(
    mut v_n_582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_583_ = l_Std_Time_Second_instToStringOffset___aux__1(v_n_582_);
    leanh::lean_dec(v_n_582_);
    return v_res_583_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOffset___aux__1(
    mut v_x_585_: *mut leanh::LeanObject,
    mut v_y_586_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_587_: u8 = 0;
    v___x_587_ = lean_int_dec_le(v_x_585_, v_y_586_);
    return v___x_587_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOffset___aux__1___boxed(
    mut v_x_588_: *mut leanh::LeanObject,
    mut v_y_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: u8 = 0;
    let mut v_r_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Std_Time_Second_instDecidableLeOffset___aux__1(v_x_588_, v_y_589_);
    leanh::lean_dec(v_y_589_);
    leanh::lean_dec(v_x_588_);
    v_r_591_ = leanh::lean_box((v_res_590_) as usize);
    return v_r_591_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOffset(
    mut v___y_592_: *mut leanh::LeanObject,
    mut v___y_593_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_594_: u8 = 0;
    v___x_594_ = lean_int_dec_le(v___y_592_, v___y_593_);
    return v___x_594_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLeOffset___boxed(
    mut v___y_595_: *mut leanh::LeanObject,
    mut v___y_596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_597_: u8 = 0;
    let mut v_r_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_597_ = l_Std_Time_Second_instDecidableLeOffset(v___y_595_, v___y_596_);
    leanh::lean_dec(v___y_596_);
    leanh::lean_dec(v___y_595_);
    v_r_598_ = leanh::lean_box((v_res_597_) as usize);
    return v_r_598_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOffset___aux__1(
    mut v_x_599_: *mut leanh::LeanObject,
    mut v_y_600_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_601_: u8 = 0;
    v___x_601_ = lean_int_dec_lt(v_x_599_, v_y_600_);
    return v___x_601_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOffset___aux__1___boxed(
    mut v_x_602_: *mut leanh::LeanObject,
    mut v_y_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_604_: u8 = 0;
    let mut v_r_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_604_ = l_Std_Time_Second_instDecidableLtOffset___aux__1(v_x_602_, v_y_603_);
    leanh::lean_dec(v_y_603_);
    leanh::lean_dec(v_x_602_);
    v_r_605_ = leanh::lean_box((v_res_604_) as usize);
    return v_r_605_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOffset(
    mut v___y_606_: *mut leanh::LeanObject,
    mut v___y_607_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_608_: u8 = 0;
    v___x_608_ = lean_int_dec_lt(v___y_606_, v___y_607_);
    return v___x_608_;
}
pub unsafe fn l_Std_Time_Second_instDecidableLtOffset___boxed(
    mut v___y_609_: *mut leanh::LeanObject,
    mut v___y_610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_611_: u8 = 0;
    let mut v_r_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Std_Time_Second_instDecidableLtOffset(v___y_609_, v___y_610_);
    leanh::lean_dec(v___y_610_);
    leanh::lean_dec(v___y_609_);
    v_r_612_ = leanh::lean_box((v_res_611_) as usize);
    return v_r_612_;
}
pub unsafe fn l_Std_Time_Second_instOfNatOffset(
    mut v_n_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_nat_to_int(v_n_613_);
    return v___x_614_;
}
pub unsafe fn l_Std_Time_Second_instOrdOffset___aux__1(
    mut v_x_615_: *mut leanh::LeanObject,
    mut v_y_616_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_617_: u8 = 0;
    v___x_617_ = lean_int_dec_lt(v_x_615_, v_y_616_);
    if v___x_617_ == 0 {
        let mut v___x_618_: u8 = 0;
        v___x_618_ = lean_int_dec_eq(v_x_615_, v_y_616_);
        if v___x_618_ == 0 {
            let mut v___x_619_: u8 = 0;
            v___x_619_ = 2;
            return v___x_619_;
        } else {
            let mut v___x_620_: u8 = 0;
            v___x_620_ = 1;
            return v___x_620_;
        }
    } else {
        let mut v___x_621_: u8 = 0;
        v___x_621_ = 0;
        return v___x_621_;
    }
}
pub unsafe fn l_Std_Time_Second_instOrdOffset___aux__1___boxed(
    mut v_x_622_: *mut leanh::LeanObject,
    mut v_y_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_624_: u8 = 0;
    let mut v_r_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Std_Time_Second_instOrdOffset___aux__1(v_x_622_, v_y_623_);
    leanh::lean_dec(v_y_623_);
    leanh::lean_dec(v_x_622_);
    v_r_625_ = leanh::lean_box((v_res_624_) as usize);
    return v_r_625_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofNat(
    mut v_data_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = lean_nat_to_int(v_data_628_);
    return v___x_629_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofInt(
    mut v_data_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_630_);
    return v_data_630_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofInt___boxed(
    mut v_data_631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_Std_Time_Second_Offset_ofInt(v_data_631_);
    leanh::lean_dec(v_data_631_);
    return v_res_632_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofInt___redArg(
    mut v_data_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_633_);
    return v_data_633_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofInt___redArg___boxed(
    mut v_data_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_635_ = l_Std_Time_Second_Ordinal_ofInt___redArg(v_data_634_);
    leanh::lean_dec(v_data_634_);
    return v_res_635_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofInt(
    mut v_leap_636_: u8,
    mut v_data_637_: *mut leanh::LeanObject,
    mut v_h_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_637_);
    return v_data_637_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofInt___boxed(
    mut v_leap_639_: *mut leanh::LeanObject,
    mut v_data_640_: *mut leanh::LeanObject,
    mut v_h_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_642_: u8 = 0;
    let mut v_res_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_642_ = (leanh::lean_unbox(v_leap_639_) as u8);
    v_res_643_ = l_Std_Time_Second_Ordinal_ofInt(v_leap_boxed_642_, v_data_640_, v_h_641_);
    leanh::lean_dec(v_data_640_);
    return v_res_643_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofNat___redArg(
    mut v_data_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = lean_nat_to_int(v_data_644_);
    return v___x_645_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofNat(
    mut v_leap_646_: u8,
    mut v_data_647_: *mut leanh::LeanObject,
    mut v_h_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = lean_nat_to_int(v_data_647_);
    return v___x_649_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofNat___boxed(
    mut v_leap_650_: *mut leanh::LeanObject,
    mut v_data_651_: *mut leanh::LeanObject,
    mut v_h_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_653_: u8 = 0;
    let mut v_res_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_653_ = (leanh::lean_unbox(v_leap_650_) as u8);
    v_res_654_ = l_Std_Time_Second_Ordinal_ofNat(v_leap_boxed_653_, v_data_651_, v_h_652_);
    return v_res_654_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofFin___redArg(
    mut v_data_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = lean_nat_to_int(v_data_655_);
    return v___x_656_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofFin(
    mut v_leap_657_: u8,
    mut v_data_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = lean_nat_to_int(v_data_658_);
    return v___x_659_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_ofFin___boxed(
    mut v_leap_660_: *mut leanh::LeanObject,
    mut v_data_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_662_: u8 = 0;
    let mut v_res_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_662_ = (leanh::lean_unbox(v_leap_660_) as u8);
    v_res_663_ = l_Std_Time_Second_Ordinal_ofFin(v_leap_boxed_662_, v_data_661_);
    return v_res_663_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_toOffset___redArg(
    mut v_ordinal_664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ordinal_664_);
    return v_ordinal_664_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_toOffset___redArg___boxed(
    mut v_ordinal_665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Std_Time_Second_Ordinal_toOffset___redArg(v_ordinal_665_);
    leanh::lean_dec(v_ordinal_665_);
    return v_res_666_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_toOffset(
    mut v_leap_667_: u8,
    mut v_ordinal_668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ordinal_668_);
    return v_ordinal_668_;
}
pub unsafe fn l_Std_Time_Second_Ordinal_toOffset___boxed(
    mut v_leap_669_: *mut leanh::LeanObject,
    mut v_ordinal_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leap_boxed_671_: u8 = 0;
    let mut v_res_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leap_boxed_671_ = (leanh::lean_unbox(v_leap_669_) as u8);
    v_res_672_ = l_Std_Time_Second_Ordinal_toOffset(v_leap_boxed_671_, v_ordinal_670_);
    leanh::lean_dec(v_ordinal_670_);
    return v_res_672_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Second(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_Second_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Second_instInhabitedOffset___aux__1();
    leanh::lean_mark_persistent(l_Std_Time_Second_instInhabitedOffset___aux__1);
    l_Std_Time_Second_instInhabitedOffset = _init_l_Std_Time_Second_instInhabitedOffset();
    leanh::lean_mark_persistent(l_Std_Time_Second_instInhabitedOffset);
    l_Std_Time_Second_instLEOffset = _init_l_Std_Time_Second_instLEOffset();
    leanh::lean_mark_persistent(l_Std_Time_Second_instLEOffset);
    l_Std_Time_Second_instLTOffset = _init_l_Std_Time_Second_instLTOffset();
    leanh::lean_mark_persistent(l_Std_Time_Second_instLTOffset);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Second(
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
pub unsafe fn initialize_Std_Time_Time_Unit_Second(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Nanosecond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Second(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Second(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Second(builtin);
}