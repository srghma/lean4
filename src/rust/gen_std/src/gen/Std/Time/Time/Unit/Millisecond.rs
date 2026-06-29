// Lean compiler output
// Module: Std.Time.Time.Unit.Millisecond
// Imports: Std.Time.Time.Unit.Nanosecond
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_instNatCast___lam__0, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::r#gen::Std::Time::Time::Unit::Nanosecond::{
    initialize_Std_Time_Time_Unit_Nanosecond, runtime_initialize_Std_Time_Time_Unit_Nanosecond,
};
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::ffi::lean_int_emod;
static mut l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Millisecond_instReprOrdinal___closed__0_value:
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
    m_fun: l_Std_Time_Millisecond_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instReprOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instReprOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instLEOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Millisecond_instLTOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Millisecond_instInhabitedOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Millisecond_instOrdOrdinal___closed__0_value:
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
    m_fun: l_Std_Time_Millisecond_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instOrdOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instOrdOrdinal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instOrdOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instReprOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instReprOrdinal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Millisecond_instInhabitedOffset___aux__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_instInhabitedOffset___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Millisecond_instInhabitedOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Millisecond_instAddOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Int_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Millisecond_instSubOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Millisecond_instNegOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instNegOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instNegOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instNegOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instLEOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Millisecond_instLTOffset: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Millisecond_instToStringOffset___closed__0_value:
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
    m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instToStringOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instToStringOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instToStringOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Millisecond_instOrdOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Millisecond_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Millisecond_instOrdOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Millisecond_instOrdOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Millisecond_instOrdOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_281_ = lean_nat_to_int(v___x_280_);
    return v___x_281_;
}
pub unsafe fn l_Std_Time_Millisecond_instReprOrdinal___aux__1(
    mut v_n_282_: *mut crate::leanh::LeanObject,
    mut v_a_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: u8 = 0;
    v___x_284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_285_ = lean_int_dec_lt(v_n_282_, v___x_284_);
    if v___x_285_ == 0 {
        let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_286_ = l_Int_repr(v_n_282_);
        v___x_287_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_287_, 0, v___x_286_);
        return v___x_287_;
    } else {
        let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_288_ = l_Int_repr(v_n_282_);
        v___x_289_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_289_, 0, v___x_288_);
        v___x_290_ = l_Repr_addAppParen(v___x_289_, v_a_283_);
        return v___x_290_;
    }
}
pub unsafe fn l_Std_Time_Millisecond_instReprOrdinal___aux__1___boxed(
    mut v_n_291_: *mut crate::leanh::LeanObject,
    mut v_a_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ = l_Std_Time_Millisecond_instReprOrdinal___aux__1(v_n_291_, v_a_292_);
    crate::leanh::lean_dec(v_a_292_);
    crate::leanh::lean_dec(v_n_291_);
    return v_res_293_;
}
pub unsafe fn l_Std_Time_Millisecond_instReprOrdinal___lam__0(
    mut v___y_294_: *mut crate::leanh::LeanObject,
    mut v___y_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: u8 = 0;
    v___x_296_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_297_ = lean_int_dec_lt(v___y_294_, v___x_296_);
    if v___x_297_ == 0 {
        let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_298_ = l_Int_repr(v___y_294_);
        v___x_299_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_299_, 0, v___x_298_);
        return v___x_299_;
    } else {
        let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_300_ = l_Int_repr(v___y_294_);
        v___x_301_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_301_, 0, v___x_300_);
        v___x_302_ = l_Repr_addAppParen(v___x_301_, v___y_295_);
        return v___x_302_;
    }
}
pub unsafe fn l_Std_Time_Millisecond_instReprOrdinal___lam__0___boxed(
    mut v___y_303_: *mut crate::leanh::LeanObject,
    mut v___y_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ = l_Std_Time_Millisecond_instReprOrdinal___lam__0(v___y_303_, v___y_304_);
    crate::leanh::lean_dec(v___y_304_);
    crate::leanh::lean_dec(v___y_303_);
    return v_res_305_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1(
    mut v_a_308_: *mut crate::leanh::LeanObject,
    mut v_b_309_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_310_: u8 = 0;
    v___x_310_ = lean_int_dec_eq(v_a_308_, v_b_309_);
    return v___x_310_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_311_: *mut crate::leanh::LeanObject,
    mut v_b_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: u8 = 0;
    let mut v_r_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Std_Time_Millisecond_instDecidableEqOrdinal___aux__1(v_a_311_, v_b_312_);
    crate::leanh::lean_dec(v_b_312_);
    crate::leanh::lean_dec(v_a_311_);
    v_r_314_ = crate::leanh::lean_box((v_res_313_) as usize);
    return v_r_314_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOrdinal(
    mut v_a_315_: *mut crate::leanh::LeanObject,
    mut v_b_316_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_317_: u8 = 0;
    v___x_317_ = lean_int_dec_eq(v_a_315_, v_b_316_);
    return v___x_317_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOrdinal___boxed(
    mut v_a_318_: *mut crate::leanh::LeanObject,
    mut v_b_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_320_: u8 = 0;
    let mut v_r_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ = l_Std_Time_Millisecond_instDecidableEqOrdinal(v_a_318_, v_b_319_);
    crate::leanh::lean_dec(v_b_319_);
    crate::leanh::lean_dec(v_a_318_);
    v_r_321_ = crate::leanh::lean_box((v_res_320_) as usize);
    return v_r_321_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instLEOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = crate::leanh::lean_box(0);
    return v___x_322_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instLTOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = crate::leanh::lean_box(0);
    return v___x_323_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = crate::leanh::lean_unsigned_to_nat(999);
    v___x_325_ = lean_nat_to_int(v___x_324_);
    return v___x_325_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_327_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_328_ = lean_int_add(v___x_327_, v___x_326_);
    return v___x_328_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_330_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_331_ = lean_int_sub(v___x_330_, v___x_329_);
    return v___x_331_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_333_ = lean_nat_to_int(v___x_332_);
    return v___x_333_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__2,
    );
    v_range_336_ = lean_int_add(v___x_335_, v___x_334_);
    return v_range_336_;
}
pub unsafe fn l_Std_Time_Millisecond_instOfNatOrdinal___aux__1(
    mut v_n_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_338_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_339_ = lean_nat_to_int(v_n_337_);
    v_range_340_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_341_ = lean_int_sub(v___x_339_, v___x_338_);
    crate::leanh::lean_dec(v___x_339_);
    v___x_342_ = lean_int_emod(v___x_341_, v_range_340_);
    crate::leanh::lean_dec(v___x_341_);
    v___x_343_ = lean_int_add(v___x_342_, v_range_340_);
    crate::leanh::lean_dec(v___x_342_);
    v___x_344_ = lean_int_emod(v___x_343_, v_range_340_);
    crate::leanh::lean_dec(v___x_343_);
    v___x_345_ = lean_int_add(v___x_344_, v___x_338_);
    crate::leanh::lean_dec(v___x_344_);
    return v___x_345_;
}
pub unsafe fn l_Std_Time_Millisecond_instOfNatOrdinal(
    mut v_n_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_348_ = lean_nat_to_int(v_n_346_);
    v_range_349_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_350_ = lean_int_sub(v___x_348_, v___x_347_);
    crate::leanh::lean_dec(v___x_348_);
    v___x_351_ = lean_int_emod(v___x_350_, v_range_349_);
    crate::leanh::lean_dec(v___x_350_);
    v___x_352_ = lean_int_add(v___x_351_, v_range_349_);
    crate::leanh::lean_dec(v___x_351_);
    v___x_353_ = lean_int_emod(v___x_352_, v_range_349_);
    crate::leanh::lean_dec(v___x_352_);
    v___x_354_ = lean_int_add(v___x_353_, v___x_347_);
    crate::leanh::lean_dec(v___x_353_);
    return v___x_354_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_356_ = lean_int_sub(v___x_355_, v___x_355_);
    return v___x_356_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v_range_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__0,
    );
    v___x_359_ = lean_int_emod(v___x_358_, v_range_357_);
    return v___x_359_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_range_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__1,
    );
    v___x_362_ = lean_int_add(v___x_361_, v_range_360_);
    return v___x_362_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_range_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Millisecond_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_364_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__2,
    );
    v___x_365_ = lean_int_emod(v___x_364_, v_range_363_);
    return v___x_365_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__3,
    );
    v___x_368_ = lean_int_add(v___x_367_, v___x_366_);
    return v___x_368_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOrdinal() -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Millisecond_instInhabitedOrdinal___closed__4,
    );
    return v___x_369_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1(
    mut v_x_370_: *mut crate::leanh::LeanObject,
    mut v_y_371_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_372_: u8 = 0;
    v___x_372_ = lean_int_dec_le(v_x_370_, v_y_371_);
    return v___x_372_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_373_: *mut crate::leanh::LeanObject,
    mut v_y_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_375_: u8 = 0;
    let mut v_r_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_375_ = l_Std_Time_Millisecond_instDecidableLeOrdinal___aux__1(v_x_373_, v_y_374_);
    crate::leanh::lean_dec(v_y_374_);
    crate::leanh::lean_dec(v_x_373_);
    v_r_376_ = crate::leanh::lean_box((v_res_375_) as usize);
    return v_r_376_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOrdinal(
    mut v___y_377_: *mut crate::leanh::LeanObject,
    mut v___y_378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_379_: u8 = 0;
    v___x_379_ = lean_int_dec_le(v___y_377_, v___y_378_);
    return v___x_379_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOrdinal___boxed(
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_382_: u8 = 0;
    let mut v_r_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ = l_Std_Time_Millisecond_instDecidableLeOrdinal(v___y_380_, v___y_381_);
    crate::leanh::lean_dec(v___y_381_);
    crate::leanh::lean_dec(v___y_380_);
    v_r_383_ = crate::leanh::lean_box((v_res_382_) as usize);
    return v_r_383_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1(
    mut v_x_384_: *mut crate::leanh::LeanObject,
    mut v_y_385_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_386_: u8 = 0;
    v___x_386_ = lean_int_dec_lt(v_x_384_, v_y_385_);
    return v___x_386_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_387_: *mut crate::leanh::LeanObject,
    mut v_y_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_389_: u8 = 0;
    let mut v_r_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_389_ = l_Std_Time_Millisecond_instDecidableLtOrdinal___aux__1(v_x_387_, v_y_388_);
    crate::leanh::lean_dec(v_y_388_);
    crate::leanh::lean_dec(v_x_387_);
    v_r_390_ = crate::leanh::lean_box((v_res_389_) as usize);
    return v_r_390_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOrdinal(
    mut v___y_391_: *mut crate::leanh::LeanObject,
    mut v___y_392_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_393_: u8 = 0;
    v___x_393_ = lean_int_dec_lt(v___y_391_, v___y_392_);
    return v___x_393_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOrdinal___boxed(
    mut v___y_394_: *mut crate::leanh::LeanObject,
    mut v___y_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_396_: u8 = 0;
    let mut v_r_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Std_Time_Millisecond_instDecidableLtOrdinal(v___y_394_, v___y_395_);
    crate::leanh::lean_dec(v___y_395_);
    crate::leanh::lean_dec(v___y_394_);
    v_r_397_ = crate::leanh::lean_box((v_res_396_) as usize);
    return v_r_397_;
}
pub unsafe fn l_Std_Time_Millisecond_instOrdOrdinal___aux__1(
    mut v_x_398_: *mut crate::leanh::LeanObject,
    mut v_y_399_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_400_: u8 = 0;
    v___x_400_ = lean_int_dec_lt(v_x_398_, v_y_399_);
    if v___x_400_ == 0 {
        let mut v___x_401_: u8 = 0;
        v___x_401_ = lean_int_dec_eq(v_x_398_, v_y_399_);
        if v___x_401_ == 0 {
            let mut v___x_402_: u8 = 0;
            v___x_402_ = 2;
            return v___x_402_;
        } else {
            let mut v___x_403_: u8 = 0;
            v___x_403_ = 1;
            return v___x_403_;
        }
    } else {
        let mut v___x_404_: u8 = 0;
        v___x_404_ = 0;
        return v___x_404_;
    }
}
pub unsafe fn l_Std_Time_Millisecond_instOrdOrdinal___aux__1___boxed(
    mut v_x_405_: *mut crate::leanh::LeanObject,
    mut v_y_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_407_: u8 = 0;
    let mut v_r_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_407_ = l_Std_Time_Millisecond_instOrdOrdinal___aux__1(v_x_405_, v_y_406_);
    crate::leanh::lean_dec(v_y_406_);
    crate::leanh::lean_dec(v_x_405_);
    v_r_408_ = crate::leanh::lean_box((v_res_407_) as usize);
    return v_r_408_;
}
pub unsafe fn l_Std_Time_Millisecond_instReprOffset___aux__1(
    mut v_x_411_: *mut crate::leanh::LeanObject,
    mut v_p_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: u8 = 0;
    v___x_413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Millisecond_instReprOrdinal___aux__1___closed__0,
    );
    v___x_414_ = lean_int_dec_lt(v_x_411_, v___x_413_);
    if v___x_414_ == 0 {
        let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_415_ = l_Int_repr(v_x_411_);
        v___x_416_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_416_, 0, v___x_415_);
        return v___x_416_;
    } else {
        let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_417_ = l_Int_repr(v_x_411_);
        v___x_418_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_418_, 0, v___x_417_);
        v___x_419_ = l_Repr_addAppParen(v___x_418_, v_p_412_);
        return v___x_419_;
    }
}
pub unsafe fn l_Std_Time_Millisecond_instReprOffset___aux__1___boxed(
    mut v_x_420_: *mut crate::leanh::LeanObject,
    mut v_p_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_422_ = l_Std_Time_Millisecond_instReprOffset___aux__1(v_x_420_, v_p_421_);
    crate::leanh::lean_dec(v_p_421_);
    crate::leanh::lean_dec(v_x_420_);
    return v_res_422_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOffset___aux__1(
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_b_425_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_426_: u8 = 0;
    v___x_426_ = lean_int_dec_eq(v_a_424_, v_b_425_);
    return v___x_426_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOffset___aux__1___boxed(
    mut v_a_427_: *mut crate::leanh::LeanObject,
    mut v_b_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_429_: u8 = 0;
    let mut v_r_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Std_Time_Millisecond_instDecidableEqOffset___aux__1(v_a_427_, v_b_428_);
    crate::leanh::lean_dec(v_b_428_);
    crate::leanh::lean_dec(v_a_427_);
    v_r_430_ = crate::leanh::lean_box((v_res_429_) as usize);
    return v_r_430_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Millisecond_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = lean_nat_to_int(v_a_431_);
    return v___x_432_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Millisecond_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = lean_nat_to_int(v_a_433_);
    v___x_435_ = l_Rat_ofInt(v___x_434_);
    return v___x_435_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOffset(
    mut v_a_436_: *mut crate::leanh::LeanObject,
    mut v_b_437_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_438_: u8 = 0;
    v___x_438_ = lean_int_dec_eq(v_a_436_, v_b_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableEqOffset___boxed(
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v_b_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_441_: u8 = 0;
    let mut v_r_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_441_ = l_Std_Time_Millisecond_instDecidableEqOffset(v_a_439_, v_b_440_);
    crate::leanh::lean_dec(v_b_440_);
    crate::leanh::lean_dec(v_a_439_);
    v_r_442_ = crate::leanh::lean_box((v_res_441_) as usize);
    return v_r_442_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_444_ = l_Rat_instNatCast___lam__0(v___x_443_);
    return v___x_444_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_446_ = l_Rat_instNatCast___lam__0(v___x_445_);
    return v___x_446_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1_once
        ),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__1,
    );
    v___x_448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0_once
        ),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_449_ = l_Rat_div(v___x_448_, v___x_447_);
    return v___x_449_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2_once
        ),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__2,
    );
    v___x_451_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_450_);
    return v___x_451_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3),
        core::ptr::addr_of_mut!(
            l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3_once
        ),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1___closed__3,
    );
    return v___x_452_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_454_ =
        l_Nat_cast___at___00Std_Time_Millisecond_instDecidableEqOffset___aux__1_spec__0(v___x_453_);
    return v___x_454_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_456_ =
        l_Nat_cast___at___00Std_Time_Millisecond_instDecidableEqOffset___aux__1_spec__0(v___x_455_);
    return v___x_456_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__1,
    );
    v___x_458_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__0,
    );
    v___x_459_ = l_Rat_div(v___x_458_, v___x_457_);
    return v___x_459_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__2_once),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__2,
    );
    v___x_461_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_460_);
    return v___x_461_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instInhabitedOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_instInhabitedOffset___closed__3_once),
        _init_l_Std_Time_Millisecond_instInhabitedOffset___closed__3,
    );
    return v___x_462_;
}
pub unsafe fn l_Std_Time_Millisecond_instAddOffset___aux__1(
    mut v_u1_463_: *mut crate::leanh::LeanObject,
    mut v_u2_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = lean_int_add(v_u1_463_, v_u2_464_);
    return v___x_465_;
}
pub unsafe fn l_Std_Time_Millisecond_instAddOffset___aux__1___boxed(
    mut v_u1_466_: *mut crate::leanh::LeanObject,
    mut v_u2_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_468_ = l_Std_Time_Millisecond_instAddOffset___aux__1(v_u1_466_, v_u2_467_);
    crate::leanh::lean_dec(v_u2_467_);
    crate::leanh::lean_dec(v_u1_466_);
    return v_res_468_;
}
pub unsafe fn l_Std_Time_Millisecond_instSubOffset___aux__1(
    mut v_u1_471_: *mut crate::leanh::LeanObject,
    mut v_u2_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = lean_int_sub(v_u1_471_, v_u2_472_);
    return v___x_473_;
}
pub unsafe fn l_Std_Time_Millisecond_instSubOffset___aux__1___boxed(
    mut v_u1_474_: *mut crate::leanh::LeanObject,
    mut v_u2_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Std_Time_Millisecond_instSubOffset___aux__1(v_u1_474_, v_u2_475_);
    crate::leanh::lean_dec(v_u2_475_);
    crate::leanh::lean_dec(v_u1_474_);
    return v_res_476_;
}
pub unsafe fn l_Std_Time_Millisecond_instNegOffset___aux__1(
    mut v_x_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_int_neg(v_x_479_);
    return v___x_480_;
}
pub unsafe fn l_Std_Time_Millisecond_instNegOffset___aux__1___boxed(
    mut v_x_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Std_Time_Millisecond_instNegOffset___aux__1(v_x_481_);
    crate::leanh::lean_dec(v_x_481_);
    return v_res_482_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instLEOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = crate::leanh::lean_box(0);
    return v___x_485_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_instLTOffset() -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = crate::leanh::lean_box(0);
    return v___x_486_;
}
pub unsafe fn l_Std_Time_Millisecond_instToStringOffset___aux__1(
    mut v_n_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_488_ = l_Int_repr(v_n_487_);
    return v___x_488_;
}
pub unsafe fn l_Std_Time_Millisecond_instToStringOffset___aux__1___boxed(
    mut v_n_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Std_Time_Millisecond_instToStringOffset___aux__1(v_n_489_);
    crate::leanh::lean_dec(v_n_489_);
    return v_res_490_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOffset___aux__1(
    mut v_x_493_: *mut crate::leanh::LeanObject,
    mut v_y_494_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_495_: u8 = 0;
    v___x_495_ = lean_int_dec_le(v_x_493_, v_y_494_);
    return v___x_495_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOffset___aux__1___boxed(
    mut v_x_496_: *mut crate::leanh::LeanObject,
    mut v_y_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_498_: u8 = 0;
    let mut v_r_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_498_ = l_Std_Time_Millisecond_instDecidableLeOffset___aux__1(v_x_496_, v_y_497_);
    crate::leanh::lean_dec(v_y_497_);
    crate::leanh::lean_dec(v_x_496_);
    v_r_499_ = crate::leanh::lean_box((v_res_498_) as usize);
    return v_r_499_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOffset(
    mut v___y_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_502_: u8 = 0;
    v___x_502_ = lean_int_dec_le(v___y_500_, v___y_501_);
    return v___x_502_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLeOffset___boxed(
    mut v___y_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_505_: u8 = 0;
    let mut v_r_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_505_ = l_Std_Time_Millisecond_instDecidableLeOffset(v___y_503_, v___y_504_);
    crate::leanh::lean_dec(v___y_504_);
    crate::leanh::lean_dec(v___y_503_);
    v_r_506_ = crate::leanh::lean_box((v_res_505_) as usize);
    return v_r_506_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOffset___aux__1(
    mut v_x_507_: *mut crate::leanh::LeanObject,
    mut v_y_508_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_509_: u8 = 0;
    v___x_509_ = lean_int_dec_lt(v_x_507_, v_y_508_);
    return v___x_509_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOffset___aux__1___boxed(
    mut v_x_510_: *mut crate::leanh::LeanObject,
    mut v_y_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_512_: u8 = 0;
    let mut v_r_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_512_ = l_Std_Time_Millisecond_instDecidableLtOffset___aux__1(v_x_510_, v_y_511_);
    crate::leanh::lean_dec(v_y_511_);
    crate::leanh::lean_dec(v_x_510_);
    v_r_513_ = crate::leanh::lean_box((v_res_512_) as usize);
    return v_r_513_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOffset(
    mut v___y_514_: *mut crate::leanh::LeanObject,
    mut v___y_515_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_516_: u8 = 0;
    v___x_516_ = lean_int_dec_lt(v___y_514_, v___y_515_);
    return v___x_516_;
}
pub unsafe fn l_Std_Time_Millisecond_instDecidableLtOffset___boxed(
    mut v___y_517_: *mut crate::leanh::LeanObject,
    mut v___y_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_519_: u8 = 0;
    let mut v_r_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Std_Time_Millisecond_instDecidableLtOffset(v___y_517_, v___y_518_);
    crate::leanh::lean_dec(v___y_518_);
    crate::leanh::lean_dec(v___y_517_);
    v_r_520_ = crate::leanh::lean_box((v_res_519_) as usize);
    return v_r_520_;
}
pub unsafe fn l_Std_Time_Millisecond_instOfNatOffset(
    mut v_n_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = lean_nat_to_int(v_n_521_);
    return v___x_522_;
}
pub unsafe fn l_Std_Time_Millisecond_instOrdOffset___aux__1(
    mut v_x_523_: *mut crate::leanh::LeanObject,
    mut v_y_524_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_525_: u8 = 0;
    v___x_525_ = lean_int_dec_lt(v_x_523_, v_y_524_);
    if v___x_525_ == 0 {
        let mut v___x_526_: u8 = 0;
        v___x_526_ = lean_int_dec_eq(v_x_523_, v_y_524_);
        if v___x_526_ == 0 {
            let mut v___x_527_: u8 = 0;
            v___x_527_ = 2;
            return v___x_527_;
        } else {
            let mut v___x_528_: u8 = 0;
            v___x_528_ = 1;
            return v___x_528_;
        }
    } else {
        let mut v___x_529_: u8 = 0;
        v___x_529_ = 0;
        return v___x_529_;
    }
}
pub unsafe fn l_Std_Time_Millisecond_instOrdOffset___aux__1___boxed(
    mut v_x_530_: *mut crate::leanh::LeanObject,
    mut v_y_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_532_: u8 = 0;
    let mut v_r_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Std_Time_Millisecond_instOrdOffset___aux__1(v_x_530_, v_y_531_);
    crate::leanh::lean_dec(v_y_531_);
    crate::leanh::lean_dec(v_x_530_);
    v_r_533_ = crate::leanh::lean_box((v_res_532_) as usize);
    return v_r_533_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofNat(
    mut v_data_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = lean_nat_to_int(v_data_536_);
    return v___x_537_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofInt(
    mut v_data_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_538_);
    return v_data_538_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofInt___boxed(
    mut v_data_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Std_Time_Millisecond_Offset_ofInt(v_data_539_);
    crate::leanh::lean_dec(v_data_539_);
    return v_res_540_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofInt___redArg(
    mut v_data_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_541_);
    return v_data_541_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofInt___redArg___boxed(
    mut v_data_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ = l_Std_Time_Millisecond_Ordinal_ofInt___redArg(v_data_542_);
    crate::leanh::lean_dec(v_data_542_);
    return v_res_543_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofInt(
    mut v_data_544_: *mut crate::leanh::LeanObject,
    mut v_h_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_data_544_);
    return v_data_544_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofInt___boxed(
    mut v_data_546_: *mut crate::leanh::LeanObject,
    mut v_h_547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_548_ = l_Std_Time_Millisecond_Ordinal_ofInt(v_data_546_, v_h_547_);
    crate::leanh::lean_dec(v_data_546_);
    return v_res_548_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofNat___redArg(
    mut v_data_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = lean_nat_to_int(v_data_549_);
    return v___x_550_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofNat(
    mut v_data_551_: *mut crate::leanh::LeanObject,
    mut v_h_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = lean_nat_to_int(v_data_551_);
    return v___x_553_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_ofFin(
    mut v_data_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = lean_nat_to_int(v_data_554_);
    return v___x_555_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_toOffset(
    mut v_ordinal_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ordinal_556_);
    return v_ordinal_556_;
}
pub unsafe fn l_Std_Time_Millisecond_Ordinal_toOffset___boxed(
    mut v_ordinal_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Std_Time_Millisecond_Ordinal_toOffset(v_ordinal_557_);
    crate::leanh::lean_dec(v_ordinal_557_);
    return v_res_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Millisecond(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Nanosecond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_Millisecond_instLEOrdinal = _init_l_Std_Time_Millisecond_instLEOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instLEOrdinal);
    l_Std_Time_Millisecond_instLTOrdinal = _init_l_Std_Time_Millisecond_instLTOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instLTOrdinal);
    l_Std_Time_Millisecond_instInhabitedOrdinal =
        _init_l_Std_Time_Millisecond_instInhabitedOrdinal();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instInhabitedOrdinal);
    l_Std_Time_Millisecond_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Millisecond_instInhabitedOffset___aux__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instInhabitedOffset___aux__1);
    l_Std_Time_Millisecond_instInhabitedOffset = _init_l_Std_Time_Millisecond_instInhabitedOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instInhabitedOffset);
    l_Std_Time_Millisecond_instLEOffset = _init_l_Std_Time_Millisecond_instLEOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instLEOffset);
    l_Std_Time_Millisecond_instLTOffset = _init_l_Std_Time_Millisecond_instLTOffset();
    crate::leanh::lean_mark_persistent(l_Std_Time_Millisecond_instLTOffset);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Millisecond(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_Unit_Millisecond(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Nanosecond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Millisecond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Millisecond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Millisecond(builtin);
}
