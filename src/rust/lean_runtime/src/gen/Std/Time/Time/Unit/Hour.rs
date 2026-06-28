// Lean compiler output
// Module: Std.Time.Time.Unit.Hour
// Imports: Std.Time.Time.Unit.Minute
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_emod;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Hour_instReprOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Hour_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Hour_instReprOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instReprOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instLEOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instLTOrdinal: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOrdinal___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instInhabitedOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Hour_instOrdOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Hour_instOrdOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instOrdOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instReprOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instReprOrdinal___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instInhabitedOffset___aux__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOffset___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOffset___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_instInhabitedOffset___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_instInhabitedOffset___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instInhabitedOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Hour_instAddOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Hour_instSubOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Hour_instNegOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instNegOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instNegOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instNegOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instNegOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Hour_instToStringOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Hour_instToStringOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instToStringOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instToStringOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instToStringOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instLTOffset: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Hour_instLEOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Hour_instOrdOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Hour_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Hour_instOrdOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Hour_instOrdOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Hour_instOrdOffset___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Hour_Ordinal_toRelative___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_309_ = lean_unsigned_to_nat(0);
    v___x_310_ = lean_nat_to_int(v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___aux__1(
    mut v_n_311_: *mut LeanObject,
    mut v_a_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u8 = 0;
    v___x_313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_314_ = lean_int_dec_lt(v_n_311_, v___x_313_);
    if v___x_314_ == 0 {
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        v___x_315_ = l_Int_repr(v_n_311_);
        v___x_316_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_316_, 0, v___x_315_);
        return v___x_316_;
    } else {
        let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
        v___x_317_ = l_Int_repr(v_n_311_);
        v___x_318_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_318_, 0, v___x_317_);
        v___x_319_ = l_Repr_addAppParen(v___x_318_, v_a_312_);
        return v___x_319_;
    }
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___aux__1___boxed(
    mut v_n_320_: *mut LeanObject,
    mut v_a_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_322_: *mut LeanObject = core::ptr::null_mut();
    v_res_322_ = l_Std_Time_Hour_instReprOrdinal___aux__1(v_n_320_, v_a_321_);
    lean_dec(v_a_321_);
    lean_dec(v_n_320_);
    return v_res_322_;
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___lam__0(
    mut v___y_323_: *mut LeanObject,
    mut v___y_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: u8 = 0;
    v___x_325_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_326_ = lean_int_dec_lt(v___y_323_, v___x_325_);
    if v___x_326_ == 0 {
        let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
        v___x_327_ = l_Int_repr(v___y_323_);
        v___x_328_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_328_, 0, v___x_327_);
        return v___x_328_;
    } else {
        let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        v___x_329_ = l_Int_repr(v___y_323_);
        v___x_330_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_330_, 0, v___x_329_);
        v___x_331_ = l_Repr_addAppParen(v___x_330_, v___y_324_);
        return v___x_331_;
    }
}
pub unsafe fn l_Std_Time_Hour_instReprOrdinal___lam__0___boxed(
    mut v___y_332_: *mut LeanObject,
    mut v___y_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = l_Std_Time_Hour_instReprOrdinal___lam__0(v___y_332_, v___y_333_);
    lean_dec(v___y_333_);
    lean_dec(v___y_332_);
    return v_res_334_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal___aux__1(
    mut v_a_337_: *mut LeanObject,
    mut v_b_338_: *mut LeanObject,
) -> u8 {
    let mut v___x_339_: u8 = 0;
    v___x_339_ = lean_int_dec_eq(v_a_337_, v_b_338_);
    return v___x_339_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_340_: *mut LeanObject,
    mut v_b_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_342_: u8 = 0;
    let mut v_r_343_: *mut LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_Time_Hour_instDecidableEqOrdinal___aux__1(v_a_340_, v_b_341_);
    lean_dec(v_b_341_);
    lean_dec(v_a_340_);
    v_r_343_ = lean_box((v_res_342_) as usize);
    return v_r_343_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal(
    mut v_a_344_: *mut LeanObject,
    mut v_b_345_: *mut LeanObject,
) -> u8 {
    let mut v___x_346_: u8 = 0;
    v___x_346_ = lean_int_dec_eq(v_a_344_, v_b_345_);
    return v___x_346_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOrdinal___boxed(
    mut v_a_347_: *mut LeanObject,
    mut v_b_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_349_: u8 = 0;
    let mut v_r_350_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l_Std_Time_Hour_instDecidableEqOrdinal(v_a_347_, v_b_348_);
    lean_dec(v_b_348_);
    lean_dec(v_a_347_);
    v_r_350_ = lean_box((v_res_349_) as usize);
    return v_r_350_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLEOrdinal() -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_box(0);
    return v___x_351_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLTOrdinal() -> *mut LeanObject {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v___x_352_ = lean_box(0);
    return v___x_352_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_353_ = lean_unsigned_to_nat(23);
    v___x_354_ = lean_nat_to_int(v___x_353_);
    return v___x_354_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1() -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_357_ = lean_int_add(v___x_356_, v___x_355_);
    return v___x_357_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2() -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_360_ = lean_int_sub(v___x_359_, v___x_358_);
    return v___x_360_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3() -> *mut LeanObject {
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_361_ = lean_unsigned_to_nat(1);
    v___x_362_ = lean_nat_to_int(v___x_361_);
    return v___x_362_;
}
pub unsafe fn _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4() -> *mut LeanObject {
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_365_: *mut LeanObject = core::ptr::null_mut();
    v___x_363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_364_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__2,
    );
    v_range_365_ = lean_int_add(v___x_364_, v___x_363_);
    return v_range_365_;
}
pub unsafe fn l_Std_Time_Hour_instOfNatOrdinal___aux__1(
    mut v_n_366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    v___x_367_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_368_ = lean_nat_to_int(v_n_366_);
    v_range_369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_370_ = lean_int_sub(v___x_368_, v___x_367_);
    lean_dec(v___x_368_);
    v___x_371_ = lean_int_emod(v___x_370_, v_range_369_);
    lean_dec(v___x_370_);
    v___x_372_ = lean_int_add(v___x_371_, v_range_369_);
    lean_dec(v___x_371_);
    v___x_373_ = lean_int_emod(v___x_372_, v_range_369_);
    lean_dec(v___x_372_);
    v___x_374_ = lean_int_add(v___x_373_, v___x_367_);
    lean_dec(v___x_373_);
    return v___x_374_;
}
pub unsafe fn l_Std_Time_Hour_instOfNatOrdinal(mut v_n_375_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_377_ = lean_nat_to_int(v_n_375_);
    v_range_378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_379_ = lean_int_sub(v___x_377_, v___x_376_);
    lean_dec(v___x_377_);
    v___x_380_ = lean_int_emod(v___x_379_, v_range_378_);
    lean_dec(v___x_379_);
    v___x_381_ = lean_int_add(v___x_380_, v_range_378_);
    lean_dec(v___x_380_);
    v___x_382_ = lean_int_emod(v___x_381_, v_range_378_);
    lean_dec(v___x_381_);
    v___x_383_ = lean_int_add(v___x_382_, v___x_376_);
    lean_dec(v___x_382_);
    return v___x_383_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__0() -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_385_ = lean_int_sub(v___x_384_, v___x_384_);
    return v___x_385_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__1() -> *mut LeanObject {
    let mut v_range_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    v_range_386_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__0,
    );
    v___x_388_ = lean_int_emod(v___x_387_, v_range_386_);
    return v___x_388_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__2() -> *mut LeanObject {
    let mut v_range_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v_range_389_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_390_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__1,
    );
    v___x_391_ = lean_int_add(v___x_390_, v_range_389_);
    return v___x_391_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__3() -> *mut LeanObject {
    let mut v_range_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v_range_392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_393_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__2,
    );
    v___x_394_ = lean_int_emod(v___x_393_, v_range_392_);
    return v___x_394_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__4() -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_396_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__3,
    );
    v___x_397_ = lean_int_add(v___x_396_, v___x_395_);
    return v___x_397_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOrdinal() -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Hour_instInhabitedOrdinal___closed__4,
    );
    return v___x_398_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal___aux__1(
    mut v_x_399_: *mut LeanObject,
    mut v_y_400_: *mut LeanObject,
) -> u8 {
    let mut v___x_401_: u8 = 0;
    v___x_401_ = lean_int_dec_le(v_x_399_, v_y_400_);
    return v___x_401_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_402_: *mut LeanObject,
    mut v_y_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_404_: u8 = 0;
    let mut v_r_405_: *mut LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Std_Time_Hour_instDecidableLeOrdinal___aux__1(v_x_402_, v_y_403_);
    lean_dec(v_y_403_);
    lean_dec(v_x_402_);
    v_r_405_ = lean_box((v_res_404_) as usize);
    return v_r_405_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal(
    mut v___y_406_: *mut LeanObject,
    mut v___y_407_: *mut LeanObject,
) -> u8 {
    let mut v___x_408_: u8 = 0;
    v___x_408_ = lean_int_dec_le(v___y_406_, v___y_407_);
    return v___x_408_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOrdinal___boxed(
    mut v___y_409_: *mut LeanObject,
    mut v___y_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_411_: u8 = 0;
    let mut v_r_412_: *mut LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Std_Time_Hour_instDecidableLeOrdinal(v___y_409_, v___y_410_);
    lean_dec(v___y_410_);
    lean_dec(v___y_409_);
    v_r_412_ = lean_box((v_res_411_) as usize);
    return v_r_412_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal___aux__1(
    mut v_x_413_: *mut LeanObject,
    mut v_y_414_: *mut LeanObject,
) -> u8 {
    let mut v___x_415_: u8 = 0;
    v___x_415_ = lean_int_dec_lt(v_x_413_, v_y_414_);
    return v___x_415_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_416_: *mut LeanObject,
    mut v_y_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_418_: u8 = 0;
    let mut v_r_419_: *mut LeanObject = core::ptr::null_mut();
    v_res_418_ = l_Std_Time_Hour_instDecidableLtOrdinal___aux__1(v_x_416_, v_y_417_);
    lean_dec(v_y_417_);
    lean_dec(v_x_416_);
    v_r_419_ = lean_box((v_res_418_) as usize);
    return v_r_419_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal(
    mut v___y_420_: *mut LeanObject,
    mut v___y_421_: *mut LeanObject,
) -> u8 {
    let mut v___x_422_: u8 = 0;
    v___x_422_ = lean_int_dec_lt(v___y_420_, v___y_421_);
    return v___x_422_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOrdinal___boxed(
    mut v___y_423_: *mut LeanObject,
    mut v___y_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_425_: u8 = 0;
    let mut v_r_426_: *mut LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Std_Time_Hour_instDecidableLtOrdinal(v___y_423_, v___y_424_);
    lean_dec(v___y_424_);
    lean_dec(v___y_423_);
    v_r_426_ = lean_box((v_res_425_) as usize);
    return v_r_426_;
}
pub unsafe fn l_Std_Time_Hour_instOrdOrdinal___aux__1(
    mut v_x_427_: *mut LeanObject,
    mut v_y_428_: *mut LeanObject,
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
    mut v_x_434_: *mut LeanObject,
    mut v_y_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_436_: u8 = 0;
    let mut v_r_437_: *mut LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Time_Hour_instOrdOrdinal___aux__1(v_x_434_, v_y_435_);
    lean_dec(v_y_435_);
    lean_dec(v_x_434_);
    v_r_437_ = lean_box((v_res_436_) as usize);
    return v_r_437_;
}
pub unsafe fn l_Std_Time_Hour_instReprOffset___aux__1(
    mut v_x_440_: *mut LeanObject,
    mut v_p_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    v___x_442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instReprOrdinal___aux__1___closed__0,
    );
    v___x_443_ = lean_int_dec_lt(v_x_440_, v___x_442_);
    if v___x_443_ == 0 {
        let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        v___x_444_ = l_Int_repr(v_x_440_);
        v___x_445_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_445_, 0, v___x_444_);
        return v___x_445_;
    } else {
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
        v___x_446_ = l_Int_repr(v_x_440_);
        v___x_447_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_447_, 0, v___x_446_);
        v___x_448_ = l_Repr_addAppParen(v___x_447_, v_p_441_);
        return v___x_448_;
    }
}
pub unsafe fn l_Std_Time_Hour_instReprOffset___aux__1___boxed(
    mut v_x_449_: *mut LeanObject,
    mut v_p_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_451_: *mut LeanObject = core::ptr::null_mut();
    v_res_451_ = l_Std_Time_Hour_instReprOffset___aux__1(v_x_449_, v_p_450_);
    lean_dec(v_p_450_);
    lean_dec(v_x_449_);
    return v_res_451_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset___aux__1(
    mut v_a_453_: *mut LeanObject,
    mut v_b_454_: *mut LeanObject,
) -> u8 {
    let mut v___x_455_: u8 = 0;
    v___x_455_ = lean_int_dec_eq(v_a_453_, v_b_454_);
    return v___x_455_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset___aux__1___boxed(
    mut v_a_456_: *mut LeanObject,
    mut v_b_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_458_: u8 = 0;
    let mut v_r_459_: *mut LeanObject = core::ptr::null_mut();
    v_res_458_ = l_Std_Time_Hour_instDecidableEqOffset___aux__1(v_a_456_, v_b_457_);
    lean_dec(v_b_457_);
    lean_dec(v_a_456_);
    v_r_459_ = lean_box((v_res_458_) as usize);
    return v_r_459_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Hour_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = lean_nat_to_int(v_a_460_);
    return v___x_461_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Hour_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    v___x_463_ = lean_nat_to_int(v_a_462_);
    v___x_464_ = l_Rat_ofInt(v___x_463_);
    return v___x_464_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset(
    mut v_a_465_: *mut LeanObject,
    mut v_b_466_: *mut LeanObject,
) -> u8 {
    let mut v___x_467_: u8 = 0;
    v___x_467_ = lean_int_dec_eq(v_a_465_, v_b_466_);
    return v___x_467_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableEqOffset___boxed(
    mut v_a_468_: *mut LeanObject,
    mut v_b_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_470_: u8 = 0;
    let mut v_r_471_: *mut LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Std_Time_Hour_instDecidableEqOffset(v_a_468_, v_b_469_);
    lean_dec(v_b_469_);
    lean_dec(v_a_468_);
    v_r_471_ = lean_box((v_res_470_) as usize);
    return v_r_471_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = lean_unsigned_to_nat(3600);
    v___x_473_ = l_Rat_instNatCast___lam__0(v___x_472_);
    return v___x_473_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1() -> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_475_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_474_);
    return v___x_475_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___aux__1() -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___aux__1___closed__1,
    );
    return v___x_476_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___closed__0() -> *mut LeanObject {
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_477_ = lean_unsigned_to_nat(3600);
    v___x_478_ =
        l_Nat_cast___at___00Std_Time_Hour_instDecidableEqOffset___aux__1_spec__0(v___x_477_);
    return v___x_478_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset___closed__1() -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___closed__0,
    );
    v___x_480_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_479_);
    return v___x_480_;
}
pub unsafe fn _init_l_Std_Time_Hour_instInhabitedOffset() -> *mut LeanObject {
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_481_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Hour_instInhabitedOffset___closed__1,
    );
    return v___x_481_;
}
pub unsafe fn l_Std_Time_Hour_instAddOffset___aux__1(
    mut v_u1_482_: *mut LeanObject,
    mut v_u2_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ = lean_int_add(v_u1_482_, v_u2_483_);
    return v___x_484_;
}
pub unsafe fn l_Std_Time_Hour_instAddOffset___aux__1___boxed(
    mut v_u1_485_: *mut LeanObject,
    mut v_u2_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_487_: *mut LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Std_Time_Hour_instAddOffset___aux__1(v_u1_485_, v_u2_486_);
    lean_dec(v_u2_486_);
    lean_dec(v_u1_485_);
    return v_res_487_;
}
pub unsafe fn l_Std_Time_Hour_instSubOffset___aux__1(
    mut v_u1_490_: *mut LeanObject,
    mut v_u2_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_int_sub(v_u1_490_, v_u2_491_);
    return v___x_492_;
}
pub unsafe fn l_Std_Time_Hour_instSubOffset___aux__1___boxed(
    mut v_u1_493_: *mut LeanObject,
    mut v_u2_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_495_: *mut LeanObject = core::ptr::null_mut();
    v_res_495_ = l_Std_Time_Hour_instSubOffset___aux__1(v_u1_493_, v_u2_494_);
    lean_dec(v_u2_494_);
    lean_dec(v_u1_493_);
    return v_res_495_;
}
pub unsafe fn l_Std_Time_Hour_instNegOffset___aux__1(
    mut v_x_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_int_neg(v_x_498_);
    return v___x_499_;
}
pub unsafe fn l_Std_Time_Hour_instNegOffset___aux__1___boxed(
    mut v_x_500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_501_: *mut LeanObject = core::ptr::null_mut();
    v_res_501_ = l_Std_Time_Hour_instNegOffset___aux__1(v_x_500_);
    lean_dec(v_x_500_);
    return v_res_501_;
}
pub unsafe fn l_Std_Time_Hour_instToStringOffset___aux__1(
    mut v_n_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v___x_505_ = l_Int_repr(v_n_504_);
    return v___x_505_;
}
pub unsafe fn l_Std_Time_Hour_instToStringOffset___aux__1___boxed(
    mut v_n_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_507_: *mut LeanObject = core::ptr::null_mut();
    v_res_507_ = l_Std_Time_Hour_instToStringOffset___aux__1(v_n_506_);
    lean_dec(v_n_506_);
    return v_res_507_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLTOffset() -> *mut LeanObject {
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    v___x_510_ = lean_box(0);
    return v___x_510_;
}
pub unsafe fn _init_l_Std_Time_Hour_instLEOffset() -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_box(0);
    return v___x_511_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset___aux__1(
    mut v_x_512_: *mut LeanObject,
    mut v_y_513_: *mut LeanObject,
) -> u8 {
    let mut v___x_514_: u8 = 0;
    v___x_514_ = lean_int_dec_le(v_x_512_, v_y_513_);
    return v___x_514_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset___aux__1___boxed(
    mut v_x_515_: *mut LeanObject,
    mut v_y_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_517_: u8 = 0;
    let mut v_r_518_: *mut LeanObject = core::ptr::null_mut();
    v_res_517_ = l_Std_Time_Hour_instDecidableLeOffset___aux__1(v_x_515_, v_y_516_);
    lean_dec(v_y_516_);
    lean_dec(v_x_515_);
    v_r_518_ = lean_box((v_res_517_) as usize);
    return v_r_518_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset(
    mut v___y_519_: *mut LeanObject,
    mut v___y_520_: *mut LeanObject,
) -> u8 {
    let mut v___x_521_: u8 = 0;
    v___x_521_ = lean_int_dec_le(v___y_519_, v___y_520_);
    return v___x_521_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLeOffset___boxed(
    mut v___y_522_: *mut LeanObject,
    mut v___y_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_524_: u8 = 0;
    let mut v_r_525_: *mut LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_Time_Hour_instDecidableLeOffset(v___y_522_, v___y_523_);
    lean_dec(v___y_523_);
    lean_dec(v___y_522_);
    v_r_525_ = lean_box((v_res_524_) as usize);
    return v_r_525_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset___aux__1(
    mut v_x_526_: *mut LeanObject,
    mut v_y_527_: *mut LeanObject,
) -> u8 {
    let mut v___x_528_: u8 = 0;
    v___x_528_ = lean_int_dec_lt(v_x_526_, v_y_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset___aux__1___boxed(
    mut v_x_529_: *mut LeanObject,
    mut v_y_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_531_: u8 = 0;
    let mut v_r_532_: *mut LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Std_Time_Hour_instDecidableLtOffset___aux__1(v_x_529_, v_y_530_);
    lean_dec(v_y_530_);
    lean_dec(v_x_529_);
    v_r_532_ = lean_box((v_res_531_) as usize);
    return v_r_532_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset(
    mut v___y_533_: *mut LeanObject,
    mut v___y_534_: *mut LeanObject,
) -> u8 {
    let mut v___x_535_: u8 = 0;
    v___x_535_ = lean_int_dec_lt(v___y_533_, v___y_534_);
    return v___x_535_;
}
pub unsafe fn l_Std_Time_Hour_instDecidableLtOffset___boxed(
    mut v___y_536_: *mut LeanObject,
    mut v___y_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_538_: u8 = 0;
    let mut v_r_539_: *mut LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Std_Time_Hour_instDecidableLtOffset(v___y_536_, v___y_537_);
    lean_dec(v___y_537_);
    lean_dec(v___y_536_);
    v_r_539_ = lean_box((v_res_538_) as usize);
    return v_r_539_;
}
pub unsafe fn l_Std_Time_Hour_instOfNatOffset(mut v_n_540_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    v___x_541_ = lean_nat_to_int(v_n_540_);
    return v___x_541_;
}
pub unsafe fn l_Std_Time_Hour_instOrdOffset___aux__1(
    mut v_x_542_: *mut LeanObject,
    mut v_y_543_: *mut LeanObject,
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
    mut v_x_549_: *mut LeanObject,
    mut v_y_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_551_: u8 = 0;
    let mut v_r_552_: *mut LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Std_Time_Hour_instOrdOffset___aux__1(v_x_549_, v_y_550_);
    lean_dec(v_y_550_);
    lean_dec(v_x_549_);
    v_r_552_ = lean_box((v_res_551_) as usize);
    return v_r_552_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt___redArg(
    mut v_data_555_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_555_);
    return v_data_555_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt___redArg___boxed(
    mut v_data_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Std_Time_Hour_Ordinal_ofInt___redArg(v_data_556_);
    lean_dec(v_data_556_);
    return v_res_557_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt(
    mut v_data_558_: *mut LeanObject,
    mut v_h_559_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_558_);
    return v_data_558_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofInt___boxed(
    mut v_data_560_: *mut LeanObject,
    mut v_h_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_562_: *mut LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Std_Time_Hour_Ordinal_ofInt(v_data_560_, v_h_561_);
    lean_dec(v_data_560_);
    return v_res_562_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_toRelative___closed__0() -> *mut LeanObject {
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_563_ = lean_unsigned_to_nat(12);
    v___x_564_ = lean_nat_to_int(v___x_563_);
    return v___x_564_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_toRelative___closed__1() -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = lean_unsigned_to_nat(11);
    v___x_566_ = lean_nat_to_int(v___x_565_);
    return v___x_566_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toRelative(
    mut v_ordinal_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_568_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__0_once),
        _init_l_Std_Time_Hour_Ordinal_toRelative___closed__0,
    );
    v___x_569_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_toRelative___closed__1_once),
        _init_l_Std_Time_Hour_Ordinal_toRelative___closed__1,
    );
    v___x_571_ = lean_int_add(v_ordinal_567_, v___x_570_);
    v___x_572_ = lean_int_emod(v___x_571_, v___x_568_);
    lean_dec(v___x_571_);
    v___x_573_ = lean_int_add(v___x_572_, v___x_569_);
    lean_dec(v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toRelative___boxed(
    mut v_ordinal_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_575_: *mut LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Std_Time_Hour_Ordinal_toRelative(v_ordinal_574_);
    lean_dec(v_ordinal_574_);
    return v_res_575_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0() -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    v___x_576_ = lean_unsigned_to_nat(24);
    v___x_577_ = lean_nat_to_int(v___x_576_);
    return v___x_577_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1() -> *mut LeanObject {
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    v___x_578_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_579_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__0,
    );
    v___x_580_ = lean_int_sub(v___x_579_, v___x_578_);
    return v___x_580_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2() -> *mut LeanObject {
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_583_: *mut LeanObject = core::ptr::null_mut();
    v___x_581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_582_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1,
    );
    v_range_583_ = lean_int_add(v___x_582_, v___x_581_);
    return v_range_583_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3() -> *mut LeanObject {
    let mut v_range_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    v_range_584_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2,
    );
    v___x_585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__1,
    );
    v___x_586_ = lean_int_emod(v___x_585_, v_range_584_);
    return v___x_586_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4() -> *mut LeanObject {
    let mut v_range_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v_range_587_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2,
    );
    v___x_588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__3,
    );
    v___x_589_ = lean_int_add(v___x_588_, v_range_587_);
    return v___x_589_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5() -> *mut LeanObject {
    let mut v_range_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    v_range_590_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__2,
    );
    v___x_591_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__4,
    );
    v___x_592_ = lean_int_emod(v___x_591_, v_range_590_);
    return v___x_592_;
}
pub unsafe fn _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6() -> *mut LeanObject {
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v___x_593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_594_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5_once),
        _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__5,
    );
    v___x_595_ = lean_int_add(v___x_594_, v___x_593_);
    return v___x_595_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(
    mut v_ordinal_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: u8 = 0;
    v___x_597_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Hour_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_598_ = lean_int_dec_lt(v_ordinal_596_, v___x_597_);
    if v___x_598_ == 0 {
        lean_inc(v_ordinal_596_);
        return v_ordinal_596_;
    } else {
        let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
        v___x_599_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6),
            core::ptr::addr_of_mut!(l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6_once),
            _init_l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___closed__6,
        );
        return v___x_599_;
    }
}
pub unsafe fn l_Std_Time_Hour_Ordinal_shiftTo1BasedHour___boxed(
    mut v_ordinal_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_601_: *mut LeanObject = core::ptr::null_mut();
    v_res_601_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_ordinal_600_);
    lean_dec(v_ordinal_600_);
    return v_res_601_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofNat___redArg(
    mut v_data_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    v___x_603_ = lean_nat_to_int(v_data_602_);
    return v___x_603_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofNat(
    mut v_data_604_: *mut LeanObject,
    mut v_h_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    v___x_606_ = lean_nat_to_int(v_data_604_);
    return v___x_606_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_ofFin(mut v_data_607_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_nat_to_int(v_data_607_);
    return v___x_608_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toOffset(
    mut v_ordinal_609_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ordinal_609_);
    return v_ordinal_609_;
}
pub unsafe fn l_Std_Time_Hour_Ordinal_toOffset___boxed(
    mut v_ordinal_610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_611_: *mut LeanObject = core::ptr::null_mut();
    v_res_611_ = l_Std_Time_Hour_Ordinal_toOffset(v_ordinal_610_);
    lean_dec(v_ordinal_610_);
    return v_res_611_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofNat(mut v_data_612_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v___x_613_ = lean_nat_to_int(v_data_612_);
    return v___x_613_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofInt(mut v_data_614_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_data_614_);
    return v_data_614_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofInt___boxed(
    mut v_data_615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_616_: *mut LeanObject = core::ptr::null_mut();
    v_res_616_ = l_Std_Time_Hour_Offset_ofInt(v_data_615_);
    lean_dec(v_data_615_);
    return v_res_616_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Hour(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Minute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_Hour_instLEOrdinal = _init_l_Std_Time_Hour_instLEOrdinal();
    lean_mark_persistent(l_Std_Time_Hour_instLEOrdinal);
    l_Std_Time_Hour_instLTOrdinal = _init_l_Std_Time_Hour_instLTOrdinal();
    lean_mark_persistent(l_Std_Time_Hour_instLTOrdinal);
    l_Std_Time_Hour_instInhabitedOrdinal = _init_l_Std_Time_Hour_instInhabitedOrdinal();
    lean_mark_persistent(l_Std_Time_Hour_instInhabitedOrdinal);
    l_Std_Time_Hour_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Hour_instInhabitedOffset___aux__1();
    lean_mark_persistent(l_Std_Time_Hour_instInhabitedOffset___aux__1);
    l_Std_Time_Hour_instInhabitedOffset = _init_l_Std_Time_Hour_instInhabitedOffset();
    lean_mark_persistent(l_Std_Time_Hour_instInhabitedOffset);
    l_Std_Time_Hour_instLTOffset = _init_l_Std_Time_Hour_instLTOffset();
    lean_mark_persistent(l_Std_Time_Hour_instLTOffset);
    l_Std_Time_Hour_instLEOffset = _init_l_Std_Time_Hour_instLEOffset();
    lean_mark_persistent(l_Std_Time_Hour_instLEOffset);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Hour(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_Unit_Hour(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Minute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Hour(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Hour(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Hour(builtin);
}
