// Lean compiler output
// Module: Std.Time.Time.Unit.Hour
// Imports: Std.Time.Time.Unit.Minute
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
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::r#gen::Std::Time::Time::Unit::Minute::{
    initialize_Std_Time_Time_Unit_Minute, runtime_initialize_Std_Time_Time_Unit_Minute,
};
static mut l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Hour_instReprOrdinal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Hour_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Hour_instReprOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instReprOrdinal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instLEOrdinal: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instLTOrdinal: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instInhabitedOrdinal: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Hour_instOrdOrdinal___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Hour_instOrdOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instOrdOrdinal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instReprOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instReprOrdinal___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instInhabitedOffset___aux__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOffset___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOffset___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOffset___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instInhabitedOffset: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Hour_instAddOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Hour_instSubOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Hour_instNegOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instNegOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instNegOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instNegOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Hour_instToStringOffset___closed__0_value: leanh::LeanClosureObject<
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
static mut l_Std_Time_Hour_instToStringOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instToStringOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instToStringOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instToStringOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instLTOffset: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instLEOffset: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Hour_instOrdOffset___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Hour_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Hour_instOrdOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Hour_instOrdOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOffset___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = leanh::lean_unsigned_to_nat(0);
    v___x_310_ = lean_nat_to_int(v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___aux__1(
    mut v_n_311_: *mut leanh::LeanObject,
    mut v_a_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u8 = 0;
    v___x_313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_314_ = lean_int_dec_lt(v_n_311_, v___x_313_);
    if v___x_314_ == 0 {
        let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_315_ = l_Int_repr(v_n_311_);
        v___x_316_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_316_, 0, v___x_315_);
        return v___x_316_;
    } else {
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_317_ = l_Int_repr(v_n_311_);
        v___x_318_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_318_, 0, v___x_317_);
        v___x_319_ = l_Repr_addAppParen(v___x_318_, v_a_312_);
        return v___x_319_;
    }
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___aux__1___boxed(
    mut v_n_320_: *mut leanh::LeanObject,
    mut v_a_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = l_Std_Time_Hour_instReprOrdinal___aux__1(v_n_320_, v_a_321_);
    leanh::lean_dec(v_a_321_);
    leanh::lean_dec(v_n_320_);
    return v_res_322_;
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___lam__0(
    mut v___y_323_: *mut leanh::LeanObject,
    mut v___y_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: u8 = 0;
    v___x_325_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_326_ = lean_int_dec_lt(v___y_323_, v___x_325_);
    if v___x_326_ == 0 {
        let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_327_ = l_Int_repr(v___y_323_);
        v___x_328_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_328_, 0, v___x_327_);
        return v___x_328_;
    } else {
        let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_329_ = l_Int_repr(v___y_323_);
        v___x_330_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_330_, 0, v___x_329_);
        v___x_331_ = l_Repr_addAppParen(v___x_330_, v___y_324_);
        return v___x_331_;
    }
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___lam__0___boxed(
    mut v___y_332_: *mut leanh::LeanObject,
    mut v___y_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l_Std_Time_Hour_instReprOrdinal___lam__0(v___y_332_, v___y_333_);
    leanh::lean_dec(v___y_333_);
    leanh::lean_dec(v___y_332_);
    return v_res_334_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal___aux__1(
    mut v_a_337_: *mut leanh::LeanObject,
    mut v_b_338_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_339_: u8 = 0;
    v___x_339_ = lean_int_dec_eq(v_a_337_, v_b_338_);
    return v___x_339_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_340_: *mut leanh::LeanObject,
    mut v_b_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_342_: u8 = 0;
    let mut v_r_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_Time_Hour_instDecidableEqOrdinal___aux__1(v_a_340_, v_b_341_);
    leanh::lean_dec(v_b_341_);
    leanh::lean_dec(v_a_340_);
    v_r_343_ = leanh::lean_box((v_res_342_) as usize);
    return v_r_343_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal(
    mut v_a_344_: *mut leanh::LeanObject,
    mut v_b_345_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_346_: u8 = 0;
    v___x_346_ = lean_int_dec_eq(v_a_344_, v_b_345_);
    return v___x_346_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal___boxed(
    mut v_a_347_: *mut leanh::LeanObject,
    mut v_b_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_349_: u8 = 0;
    let mut v_r_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_Time_Hour_instDecidableEqOrdinal(v_a_347_, v_b_348_);
    leanh::lean_dec(v_b_348_);
    leanh::lean_dec(v_a_347_);
    v_r_350_ = leanh::lean_box((v_res_349_) as usize);
    return v_r_350_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLEOrdinal() -> *mut leanh::LeanObject {
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = leanh::lean_box(0);
    return v___x_351_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLTOrdinal() -> *mut leanh::LeanObject {
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_352_ = leanh::lean_box(0);
    return v___x_352_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = leanh::lean_unsigned_to_nat(23);
    v___x_354_ = lean_nat_to_int(v___x_353_);
    return v___x_354_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_356_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_357_ = lean_int_add(v___x_356_, v___x_355_);
    return v___x_357_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_359_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_360_ = lean_int_sub(v___x_359_, v___x_358_);
    return v___x_360_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_361_ = leanh::lean_unsigned_to_nat(1);
    v___x_362_ = lean_nat_to_int(v___x_361_);
    return v___x_362_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2,
    );
    v_range_365_ = lean_int_add(v___x_364_, v___x_363_);
    return v_range_365_;
}
pub unsafe fn l_Std_Time_Hour_instOfNatOrdinal___aux__1(
    mut v_n_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_367_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_368_ = lean_nat_to_int(v_n_366_);
    v_range_369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_370_ = lean_int_sub(v___x_368_, v___x_367_);
    leanh::lean_dec(v___x_368_);
    v___x_371_ = lean_int_emod(v___x_370_, v_range_369_);
    leanh::lean_dec(v___x_370_);
    v___x_372_ = lean_int_add(v___x_371_, v_range_369_);
    leanh::lean_dec(v___x_371_);
    v___x_373_ = lean_int_emod(v___x_372_, v_range_369_);
    leanh::lean_dec(v___x_372_);
    v___x_374_ = lean_int_add(v___x_373_, v___x_367_);
    leanh::lean_dec(v___x_373_);
    return v___x_374_;
}
pub unsafe fn l_Std_Time_Hour_instOfNatOrdinal(
    mut v_n_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_377_ = lean_nat_to_int(v_n_375_);
    v_range_378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_379_ = lean_int_sub(v___x_377_, v___x_376_);
    leanh::lean_dec(v___x_377_);
    v___x_380_ = lean_int_emod(v___x_379_, v_range_378_);
    leanh::lean_dec(v___x_379_);
    v___x_381_ = lean_int_add(v___x_380_, v_range_378_);
    leanh::lean_dec(v___x_380_);
    v___x_382_ = lean_int_emod(v___x_381_, v_range_378_);
    leanh::lean_dec(v___x_381_);
    v___x_383_ = lean_int_add(v___x_382_, v___x_376_);
    leanh::lean_dec(v___x_382_);
    return v___x_383_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_385_ = lean_int_sub(v___x_384_, v___x_384_);
    return v___x_385_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__1()
-> *mut leanh::LeanObject {
    let mut v_range_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_386_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__0,
    );
    v___x_388_ = lean_int_emod(v___x_387_, v_range_386_);
    return v___x_388_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__2()
-> *mut leanh::LeanObject {
    let mut v_range_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_389_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__1,
    );
    v___x_391_ = lean_int_add(v___x_390_, v_range_389_);
    return v___x_391_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__3()
-> *mut leanh::LeanObject {
    let mut v_range_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_393_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__2,
    );
    v___x_394_ = lean_int_emod(v___x_393_, v_range_392_);
    return v___x_394_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_396_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__3,
    );
    v___x_397_ = lean_int_add(v___x_396_, v___x_395_);
    return v___x_397_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal() -> *mut leanh::LeanObject {
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__4,
    );
    return v___x_398_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal___aux__1(
    mut v_x_399_: *mut leanh::LeanObject,
    mut v_y_400_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_401_: u8 = 0;
    v___x_401_ = lean_int_dec_le(v_x_399_, v_y_400_);
    return v___x_401_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_402_: *mut leanh::LeanObject,
    mut v_y_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_404_: u8 = 0;
    let mut v_r_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Std_Time_Hour_instDecidableLeOrdinal___aux__1(v_x_402_, v_y_403_);
    leanh::lean_dec(v_y_403_);
    leanh::lean_dec(v_x_402_);
    v_r_405_ = leanh::lean_box((v_res_404_) as usize);
    return v_r_405_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal(
    mut v___y_406_: *mut leanh::LeanObject,
    mut v___y_407_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_408_: u8 = 0;
    v___x_408_ = lean_int_dec_le(v___y_406_, v___y_407_);
    return v___x_408_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal___boxed(
    mut v___y_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_411_: u8 = 0;
    let mut v_r_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Std_Time_Hour_instDecidableLeOrdinal(v___y_409_, v___y_410_);
    leanh::lean_dec(v___y_410_);
    leanh::lean_dec(v___y_409_);
    v_r_412_ = leanh::lean_box((v_res_411_) as usize);
    return v_r_412_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal___aux__1(
    mut v_x_413_: *mut leanh::LeanObject,
    mut v_y_414_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_415_: u8 = 0;
    v___x_415_ = lean_int_dec_lt(v_x_413_, v_y_414_);
    return v___x_415_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_416_: *mut leanh::LeanObject,
    mut v_y_417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_418_: u8 = 0;
    let mut v_r_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_418_ = l_Std_Time_Hour_instDecidableLtOrdinal___aux__1(v_x_416_, v_y_417_);
    leanh::lean_dec(v_y_417_);
    leanh::lean_dec(v_x_416_);
    v_r_419_ = leanh::lean_box((v_res_418_) as usize);
    return v_r_419_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal(
    mut v___y_420_: *mut leanh::LeanObject,
    mut v___y_421_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_422_: u8 = 0;
    v___x_422_ = lean_int_dec_lt(v___y_420_, v___y_421_);
    return v___x_422_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal___boxed(
    mut v___y_423_: *mut leanh::LeanObject,
    mut v___y_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_425_: u8 = 0;
    let mut v_r_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Std_Time_Hour_instDecidableLtOrdinal(v___y_423_, v___y_424_);
    leanh::lean_dec(v___y_424_);
    leanh::lean_dec(v___y_423_);
    v_r_426_ = leanh::lean_box((v_res_425_) as usize);
    return v_r_426_;
}
pub unsafe fn l_Std_Time_Hour_instOrdOrdinal___aux__1(
    mut v_x_427_: *mut leanh::LeanObject,
    mut v_y_428_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_429_: u8 = 0;
    v___x_429_ = lean_int_dec_lt(v_x_427_, v_y_428_);
    if v___x_429_ == 0 {
        let mut v___x_430_: u8 = 0;
        v___x_430_ = lean_int_dec_eq(v_x_427_, v_y_428_);
        if v___x_430_ == 0 {
            let mut v___x_431_: u8 = 0;
            v___x_431_ = 2;
            return v___x_431_;
        } else {
            let mut v___x_432_: u8 = 0;
            v___x_432_ = 1;
            return v___x_432_;
        }
    } else {
        let mut v___x_433_: u8 = 0;
        v___x_433_ = 0;
        return v___x_433_;
    }
}
pub unsafe fn l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed(
    mut v_x_434_: *mut leanh::LeanObject,
    mut v_y_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_436_: u8 = 0;
    let mut v_r_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Time_Hour_instOrdOrdinal___aux__1(v_x_434_, v_y_435_);
    leanh::lean_dec(v_y_435_);
    leanh::lean_dec(v_x_434_);
    v_r_437_ = leanh::lean_box((v_res_436_) as usize);
    return v_r_437_;
}
pub unsafe fn l_Std_Time_Hour_instReprOffset___aux__1(
    mut v_x_440_: *mut leanh::LeanObject,
    mut v_p_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    v___x_442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_443_ = lean_int_dec_lt(v_x_440_, v___x_442_);
    if v___x_443_ == 0 {
        let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_444_ = l_Int_repr(v_x_440_);
        v___x_445_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_445_, 0, v___x_444_);
        return v___x_445_;
    } else {
        let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_446_ = l_Int_repr(v_x_440_);
        v___x_447_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_447_, 0, v___x_446_);
        v___x_448_ = l_Repr_addAppParen(v___x_447_, v_p_441_);
        return v___x_448_;
    }
}
pub unsafe fn l_Std_Time_Hour_instReprOffset___aux__1___boxed(
    mut v_x_449_: *mut leanh::LeanObject,
    mut v_p_450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_451_ = l_Std_Time_Hour_instReprOffset___aux__1(v_x_449_, v_p_450_);
    leanh::lean_dec(v_p_450_);
    leanh::lean_dec(v_x_449_);
    return v_res_451_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset___aux__1(
    mut v_a_453_: *mut leanh::LeanObject,
    mut v_b_454_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_455_: u8 = 0;
    v___x_455_ = lean_int_dec_eq(v_a_453_, v_b_454_);
    return v___x_455_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset___aux__1___boxed(
    mut v_a_456_: *mut leanh::LeanObject,
    mut v_b_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_458_: u8 = 0;
    let mut v_r_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_458_ = l_Std_Time_Hour_instDecidableEqOffset___aux__1(v_a_456_, v_b_457_);
    leanh::lean_dec(v_b_457_);
    leanh::lean_dec(v_a_456_);
    v_r_459_ = leanh::lean_box((v_res_458_) as usize);
    return v_r_459_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Hour_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_461_ = lean_nat_to_int(v_a_460_);
    return v___x_461_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Hour_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = lean_nat_to_int(v_a_462_);
    v___x_464_ = l_Rat_ofInt(v___x_463_);
    return v___x_464_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset(
    mut v_a_465_: *mut leanh::LeanObject,
    mut v_b_466_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_467_: u8 = 0;
    v___x_467_ = lean_int_dec_eq(v_a_465_, v_b_466_);
    return v___x_467_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset___boxed(
    mut v_a_468_: *mut leanh::LeanObject,
    mut v_b_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_470_: u8 = 0;
    let mut v_r_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Std_Time_Hour_instDecidableEqOffset(v_a_468_, v_b_469_);
    leanh::lean_dec(v_b_469_);
    leanh::lean_dec(v_a_468_);
    v_r_471_ = leanh::lean_box((v_res_470_) as usize);
    return v_r_471_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = leanh::lean_unsigned_to_nat(3600);
    v___x_473_ = l_Rat_instNatCast___lam__0(v___x_472_);
    return v___x_473_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_475_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_474_);
    return v___x_475_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___aux__1() -> *mut leanh::LeanObject
{
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1,
    );
    return v___x_476_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_477_ = leanh::lean_unsigned_to_nat(3600);
    v___x_478_ =
        l_Nat_cast___at___00Std_Time_Hour_instDecidableEqOffset___aux__1_spec__0(v___x_477_);
    return v___x_478_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___closed__0,
    );
    v___x_480_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_479_);
    return v___x_480_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset() -> *mut leanh::LeanObject {
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___closed__1,
    );
    return v___x_481_;
}
pub unsafe fn l_Std_Time_Hour_instAddOffset___aux__1(
    mut v_u1_482_: *mut leanh::LeanObject,
    mut v_u2_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_484_ = lean_int_add(v_u1_482_, v_u2_483_);
    return v___x_484_;
}
pub unsafe fn l_Std_Time_Hour_instAddOffset___aux__1___boxed(
    mut v_u1_485_: *mut leanh::LeanObject,
    mut v_u2_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Std_Time_Hour_instAddOffset___aux__1(v_u1_485_, v_u2_486_);
    leanh::lean_dec(v_u2_486_);
    leanh::lean_dec(v_u1_485_);
    return v_res_487_;
}
pub unsafe fn l_Std_Time_Hour_instSubOffset___aux__1(
    mut v_u1_490_: *mut leanh::LeanObject,
    mut v_u2_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_int_sub(v_u1_490_, v_u2_491_);
    return v___x_492_;
}
pub unsafe fn l_Std_Time_Hour_instSubOffset___aux__1___boxed(
    mut v_u1_493_: *mut leanh::LeanObject,
    mut v_u2_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_495_ = l_Std_Time_Hour_instSubOffset___aux__1(v_u1_493_, v_u2_494_);
    leanh::lean_dec(v_u2_494_);
    leanh::lean_dec(v_u1_493_);
    return v_res_495_;
}
pub unsafe fn l_Std_Time_Hour_instNegOffset___aux__1(
    mut v_x_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_int_neg(v_x_498_);
    return v___x_499_;
}
pub unsafe fn l_Std_Time_Hour_instNegOffset___aux__1___boxed(
    mut v_x_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_501_ = l_Std_Time_Hour_instNegOffset___aux__1(v_x_500_);
    leanh::lean_dec(v_x_500_);
    return v_res_501_;
}
pub unsafe fn l_Std_Time_Hour_instToStringOffset___aux__1(
    mut v_n_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_505_ = l_Int_repr(v_n_504_);
    return v___x_505_;
}
pub unsafe fn l_Std_Time_Hour_instToStringOffset___aux__1___boxed(
    mut v_n_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_507_ = l_Std_Time_Hour_instToStringOffset___aux__1(v_n_506_);
    leanh::lean_dec(v_n_506_);
    return v_res_507_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLTOffset() -> *mut leanh::LeanObject {
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = leanh::lean_box(0);
    return v___x_510_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLEOffset() -> *mut leanh::LeanObject {
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = leanh::lean_box(0);
    return v___x_511_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset___aux__1(
    mut v_x_512_: *mut leanh::LeanObject,
    mut v_y_513_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_514_: u8 = 0;
    v___x_514_ = lean_int_dec_le(v_x_512_, v_y_513_);
    return v___x_514_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset___aux__1___boxed(
    mut v_x_515_: *mut leanh::LeanObject,
    mut v_y_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_517_: u8 = 0;
    let mut v_r_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_517_ = l_Std_Time_Hour_instDecidableLeOffset___aux__1(v_x_515_, v_y_516_);
    leanh::lean_dec(v_y_516_);
    leanh::lean_dec(v_x_515_);
    v_r_518_ = leanh::lean_box((v_res_517_) as usize);
    return v_r_518_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset(
    mut v___y_519_: *mut leanh::LeanObject,
    mut v___y_520_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_521_: u8 = 0;
    v___x_521_ = lean_int_dec_le(v___y_519_, v___y_520_);
    return v___x_521_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset___boxed(
    mut v___y_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: u8 = 0;
    let mut v_r_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_Time_Hour_instDecidableLeOffset(v___y_522_, v___y_523_);
    leanh::lean_dec(v___y_523_);
    leanh::lean_dec(v___y_522_);
    v_r_525_ = leanh::lean_box((v_res_524_) as usize);
    return v_r_525_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset___aux__1(
    mut v_x_526_: *mut leanh::LeanObject,
    mut v_y_527_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_528_: u8 = 0;
    v___x_528_ = lean_int_dec_lt(v_x_526_, v_y_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset___aux__1___boxed(
    mut v_x_529_: *mut leanh::LeanObject,
    mut v_y_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_531_: u8 = 0;
    let mut v_r_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Std_Time_Hour_instDecidableLtOffset___aux__1(v_x_529_, v_y_530_);
    leanh::lean_dec(v_y_530_);
    leanh::lean_dec(v_x_529_);
    v_r_532_ = leanh::lean_box((v_res_531_) as usize);
    return v_r_532_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset(
    mut v___y_533_: *mut leanh::LeanObject,
    mut v___y_534_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_535_: u8 = 0;
    v___x_535_ = lean_int_dec_lt(v___y_533_, v___y_534_);
    return v___x_535_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset___boxed(
    mut v___y_536_: *mut leanh::LeanObject,
    mut v___y_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_538_: u8 = 0;
    let mut v_r_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Std_Time_Hour_instDecidableLtOffset(v___y_536_, v___y_537_);
    leanh::lean_dec(v___y_537_);
    leanh::lean_dec(v___y_536_);
    v_r_539_ = leanh::lean_box((v_res_538_) as usize);
    return v_r_539_;
}
pub unsafe fn l_Std_Time_Hour_instOfNatOffset(
    mut v_n_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = lean_nat_to_int(v_n_540_);
    return v___x_541_;
}
pub unsafe fn l_Std_Time_Hour_instOrdOffset___aux__1(
    mut v_x_542_: *mut leanh::LeanObject,
    mut v_y_543_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_544_: u8 = 0;
    v___x_544_ = lean_int_dec_lt(v_x_542_, v_y_543_);
    if v___x_544_ == 0 {
        let mut v___x_545_: u8 = 0;
        v___x_545_ = lean_int_dec_eq(v_x_542_, v_y_543_);
        if v___x_545_ == 0 {
            let mut v___x_546_: u8 = 0;
            v___x_546_ = 2;
            return v___x_546_;
        } else {
            let mut v___x_547_: u8 = 0;
            v___x_547_ = 1;
            return v___x_547_;
        }
    } else {
        let mut v___x_548_: u8 = 0;
        v___x_548_ = 0;
        return v___x_548_;
    }
}
pub unsafe fn l_Std_Time_Hour_instOrdOffset___aux__1___boxed(
    mut v_x_549_: *mut leanh::LeanObject,
    mut v_y_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_551_: u8 = 0;
    let mut v_r_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Std_Time_Hour_instOrdOffset___aux__1(v_x_549_, v_y_550_);
    leanh::lean_dec(v_y_550_);
    leanh::lean_dec(v_x_549_);
    v_r_552_ = leanh::lean_box((v_res_551_) as usize);
    return v_r_552_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt___redArg(
    mut v_data_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_555_);
    return v_data_555_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt___redArg___boxed(
    mut v_data_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Std_Time_Hour_Ordinal_ofInt___redArg(v_data_556_);
    leanh::lean_dec(v_data_556_);
    return v_res_557_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt(
    mut v_data_558_: *mut leanh::LeanObject,
    mut v_h_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_558_);
    return v_data_558_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt___boxed(
    mut v_data_560_: *mut leanh::LeanObject,
    mut v_h_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Std_Time_Hour_Ordinal_ofInt(v_data_560_, v_h_561_);
    leanh::lean_dec(v_data_560_);
    return v_res_562_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_toRelative___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = leanh::lean_unsigned_to_nat(12);
    v___x_564_ = lean_nat_to_int(v___x_563_);
    return v___x_564_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_toRelative___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = leanh::lean_unsigned_to_nat(11);
    v___x_566_ = lean_nat_to_int(v___x_565_);
    return v___x_566_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toRelative(
    mut v_ordinal_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__0_once),
        _init_l_Std_Time_Hour_Ordinal_toRelative___closed__0,
    );
    v___x_569_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_570_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__1_once),
        _init_l_Std_Time_Hour_Ordinal_toRelative___closed__1,
    );
    v___x_571_ = lean_int_add(v_ordinal_567_, v___x_570_);
    v___x_572_ = lean_int_emod(v___x_571_, v___x_568_);
    leanh::lean_dec(v___x_571_);
    v___x_573_ = lean_int_add(v___x_572_, v___x_569_);
    leanh::lean_dec(v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toRelative___boxed(
    mut v_ordinal_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Std_Time_Hour_Ordinal_toRelative(v_ordinal_574_);
    leanh::lean_dec(v_ordinal_574_);
    return v_res_575_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = leanh::lean_unsigned_to_nat(24);
    v___x_577_ = lean_nat_to_int(v___x_576_);
    return v___x_577_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_579_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0,
    );
    v___x_580_ = lean_int_sub(v___x_579_, v___x_578_);
    return v___x_580_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_582_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1,
    );
    v_range_583_ = lean_int_add(v___x_582_, v___x_581_);
    return v_range_583_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3()
-> *mut leanh::LeanObject {
    let mut v_range_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_584_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2,
    );
    v___x_585_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1,
    );
    v___x_586_ = lean_int_emod(v___x_585_, v_range_584_);
    return v___x_586_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4()
-> *mut leanh::LeanObject {
    let mut v_range_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_587_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2,
    );
    v___x_588_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3,
    );
    v___x_589_ = lean_int_add(v___x_588_, v_range_587_);
    return v___x_589_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5()
-> *mut leanh::LeanObject {
    let mut v_range_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_590_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2,
    );
    v___x_591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4,
    );
    v___x_592_ = lean_int_emod(v___x_591_, v_range_590_);
    return v___x_592_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_593_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_594_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5,
    );
    v___x_595_ = lean_int_add(v___x_594_, v___x_593_);
    return v___x_595_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(
    mut v_ordinal_596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: u8 = 0;
    v___x_597_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_598_ = lean_int_dec_lt(v_ordinal_596_, v___x_597_);
    if v___x_598_ == 0 {
        leanh::lean_inc(v_ordinal_596_);
        return v_ordinal_596_;
    } else {
        let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_599_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6),
            core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6_once),
            _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6,
        );
        return v___x_599_;
    }
}
pub unsafe fn l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___boxed(
    mut v_ordinal_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_601_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_ordinal_600_);
    leanh::lean_dec(v_ordinal_600_);
    return v_res_601_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofNat___redArg(
    mut v_data_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = lean_nat_to_int(v_data_602_);
    return v___x_603_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofNat(
    mut v_data_604_: *mut leanh::LeanObject,
    mut v_h_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = lean_nat_to_int(v_data_604_);
    return v___x_606_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofFin(
    mut v_data_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_nat_to_int(v_data_607_);
    return v___x_608_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toOffset(
    mut v_ordinal_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ordinal_609_);
    return v_ordinal_609_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toOffset___boxed(
    mut v_ordinal_610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Std_Time_Hour_Ordinal_toOffset(v_ordinal_610_);
    leanh::lean_dec(v_ordinal_610_);
    return v_res_611_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofNat(
    mut v_data_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_613_ = lean_nat_to_int(v_data_612_);
    return v___x_613_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofInt(
    mut v_data_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_data_614_);
    return v_data_614_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofInt___boxed(
    mut v_data_615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_616_ = l_Std_Time_Hour_Offset_ofInt(v_data_615_);
    leanh::lean_dec(v_data_615_);
    return v_res_616_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Hour(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Minute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_Hour_instLEOrdinal = _init_l_Std_Time_Hour_instLEOrdinal();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instLEOrdinal);
    l_Std_Time_Hour_instLTOrdinal = _init_l_Std_Time_Hour_instLTOrdinal();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instLTOrdinal);
    l_Std_Time_Hour_instInhabitedOrdinal = _init_l_Std_Time_Hour_instInhabitedOrdinal();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instInhabitedOrdinal);
    l_Std_Time_Hour_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Hour_instInhabitedOffset___aux__1();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instInhabitedOffset___aux__1);
    l_Std_Time_Hour_instInhabitedOffset = _init_l_Std_Time_Hour_instInhabitedOffset();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instInhabitedOffset);
    l_Std_Time_Hour_instLTOffset = _init_l_Std_Time_Hour_instLTOffset();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instLTOffset);
    l_Std_Time_Hour_instLEOffset = _init_l_Std_Time_Hour_instLEOffset();
    leanh::lean_mark_persistent(l_Std_Time_Hour_instLEOffset);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Hour(
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
pub unsafe fn initialize_Std_Time_Time_Unit_Hour(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Minute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Hour(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Hour(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Hour(builtin);
}