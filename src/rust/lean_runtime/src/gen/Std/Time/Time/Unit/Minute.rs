// Lean compiler output
// Module: Std.Time.Time.Unit.Minute
// Imports: Std.Time.Time.Unit.Second
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_neg___boxed, l_Int_sub___boxed,
};
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_instNatCast___lam__0, l_Rat_ofInt};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Internal::UnitVal::l_Std_Time_Internal_instInhabitedUnitVal_default;
use crate::r#gen::Std::Time::Time::Unit::Second::{
    initialize_Std_Time_Time_Unit_Second, runtime_initialize_Std_Time_Time_Unit_Second,
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
static mut l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Minute_instReprOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Minute_instReprOrdinal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Minute_instReprOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instReprOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instReprOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instLEOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Minute_instLTOrdinal: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOrdinal___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Minute_instInhabitedOrdinal: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Minute_instOrdOrdinal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Minute_instOrdOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instOrdOrdinal: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instOrdOrdinal___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instReprOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instReprOrdinal___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Minute_instInhabitedOffset___aux__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOffset___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOffset___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Minute_instInhabitedOffset___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Minute_instInhabitedOffset___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Minute_instInhabitedOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Minute_instAddOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Minute_instAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Minute_instSubOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Minute_instSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Minute_instNegOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Minute_instNegOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instNegOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instNegOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instNegOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Minute_instToStringOffset___closed__0_value: LeanClosureObject<0> =
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
static mut l_Std_Time_Minute_instToStringOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instToStringOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instToStringOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instToStringOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instLTOffset: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Minute_instLEOffset: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Minute_instOrdOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Minute_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Minute_instOrdOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instOrdOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_Minute_instOrdOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Minute_instOrdOffset___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = lean_unsigned_to_nat(0);
    v___x_271_ = lean_nat_to_int(v___x_270_);
    return v___x_271_;
}
pub unsafe fn l_Std_Time_Minute_instReprOrdinal___aux__1(
    mut v_n_272_: *mut LeanObject,
    mut v_a_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: u8 = 0;
    v___x_274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_275_ = lean_int_dec_lt(v_n_272_, v___x_274_);
    if v___x_275_ == 0 {
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        v___x_276_ = l_Int_repr(v_n_272_);
        v___x_277_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_277_, 0, v___x_276_);
        return v___x_277_;
    } else {
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        v___x_278_ = l_Int_repr(v_n_272_);
        v___x_279_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_279_, 0, v___x_278_);
        v___x_280_ = l_Repr_addAppParen(v___x_279_, v_a_273_);
        return v___x_280_;
    }
}
pub unsafe fn l_Std_Time_Minute_instReprOrdinal___aux__1___boxed(
    mut v_n_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_283_: *mut LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Std_Time_Minute_instReprOrdinal___aux__1(v_n_281_, v_a_282_);
    lean_dec(v_a_282_);
    lean_dec(v_n_281_);
    return v_res_283_;
}
pub unsafe fn l_Std_Time_Minute_instReprOrdinal___lam__0(
    mut v___y_284_: *mut LeanObject,
    mut v___y_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: u8 = 0;
    v___x_286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_287_ = lean_int_dec_lt(v___y_284_, v___x_286_);
    if v___x_287_ == 0 {
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        v___x_288_ = l_Int_repr(v___y_284_);
        v___x_289_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_289_, 0, v___x_288_);
        return v___x_289_;
    } else {
        let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        v___x_290_ = l_Int_repr(v___y_284_);
        v___x_291_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_291_, 0, v___x_290_);
        v___x_292_ = l_Repr_addAppParen(v___x_291_, v___y_285_);
        return v___x_292_;
    }
}
pub unsafe fn l_Std_Time_Minute_instReprOrdinal___lam__0___boxed(
    mut v___y_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Std_Time_Minute_instReprOrdinal___lam__0(v___y_293_, v___y_294_);
    lean_dec(v___y_294_);
    lean_dec(v___y_293_);
    return v_res_295_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOrdinal___aux__1(
    mut v_a_298_: *mut LeanObject,
    mut v_b_299_: *mut LeanObject,
) -> u8 {
    let mut v___x_300_: u8 = 0;
    v___x_300_ = lean_int_dec_eq(v_a_298_, v_b_299_);
    return v___x_300_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOrdinal___aux__1___boxed(
    mut v_a_301_: *mut LeanObject,
    mut v_b_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_303_: u8 = 0;
    let mut v_r_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Std_Time_Minute_instDecidableEqOrdinal___aux__1(v_a_301_, v_b_302_);
    lean_dec(v_b_302_);
    lean_dec(v_a_301_);
    v_r_304_ = lean_box((v_res_303_) as usize);
    return v_r_304_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOrdinal(
    mut v_a_305_: *mut LeanObject,
    mut v_b_306_: *mut LeanObject,
) -> u8 {
    let mut v___x_307_: u8 = 0;
    v___x_307_ = lean_int_dec_eq(v_a_305_, v_b_306_);
    return v___x_307_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOrdinal___boxed(
    mut v_a_308_: *mut LeanObject,
    mut v_b_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_310_: u8 = 0;
    let mut v_r_311_: *mut LeanObject = core::ptr::null_mut();
    v_res_310_ = l_Std_Time_Minute_instDecidableEqOrdinal(v_a_308_, v_b_309_);
    lean_dec(v_b_309_);
    lean_dec(v_a_308_);
    v_r_311_ = lean_box((v_res_310_) as usize);
    return v_r_311_;
}
pub unsafe fn _init_l_Std_Time_Minute_instLEOrdinal() -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = lean_box(0);
    return v___x_312_;
}
pub unsafe fn _init_l_Std_Time_Minute_instLTOrdinal() -> *mut LeanObject {
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    v___x_313_ = lean_box(0);
    return v___x_313_;
}
pub unsafe fn _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__0() -> *mut LeanObject {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v___x_314_ = lean_unsigned_to_nat(59);
    v___x_315_ = lean_nat_to_int(v___x_314_);
    return v___x_315_;
}
pub unsafe fn _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__1() -> *mut LeanObject {
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_316_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__0,
    );
    v___x_317_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_318_ = lean_int_add(v___x_317_, v___x_316_);
    return v___x_318_;
}
pub unsafe fn _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__2() -> *mut LeanObject {
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_320_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__1_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__1,
    );
    v___x_321_ = lean_int_sub(v___x_320_, v___x_319_);
    return v___x_321_;
}
pub unsafe fn _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__3() -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_unsigned_to_nat(1);
    v___x_323_ = lean_nat_to_int(v___x_322_);
    return v___x_323_;
}
pub unsafe fn _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4() -> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_326_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__3_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__3,
    );
    v___x_325_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__2_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__2,
    );
    v_range_326_ = lean_int_add(v___x_325_, v___x_324_);
    return v_range_326_;
}
pub unsafe fn l_Std_Time_Minute_instOfNatOrdinal___aux__1(
    mut v_n_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_329_ = lean_nat_to_int(v_n_327_);
    v_range_330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_331_ = lean_int_sub(v___x_329_, v___x_328_);
    lean_dec(v___x_329_);
    v___x_332_ = lean_int_emod(v___x_331_, v_range_330_);
    lean_dec(v___x_331_);
    v___x_333_ = lean_int_add(v___x_332_, v_range_330_);
    lean_dec(v___x_332_);
    v___x_334_ = lean_int_emod(v___x_333_, v_range_330_);
    lean_dec(v___x_333_);
    v___x_335_ = lean_int_add(v___x_334_, v___x_328_);
    lean_dec(v___x_334_);
    return v___x_335_;
}
pub unsafe fn l_Std_Time_Minute_instOfNatOrdinal(mut v_n_336_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_338_ = lean_nat_to_int(v_n_336_);
    v_range_339_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_340_ = lean_int_sub(v___x_338_, v___x_337_);
    lean_dec(v___x_338_);
    v___x_341_ = lean_int_emod(v___x_340_, v_range_339_);
    lean_dec(v___x_340_);
    v___x_342_ = lean_int_add(v___x_341_, v_range_339_);
    lean_dec(v___x_341_);
    v___x_343_ = lean_int_emod(v___x_342_, v_range_339_);
    lean_dec(v___x_342_);
    v___x_344_ = lean_int_add(v___x_343_, v___x_337_);
    lean_dec(v___x_343_);
    return v___x_344_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__0() -> *mut LeanObject {
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    v___x_345_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_346_ = lean_int_sub(v___x_345_, v___x_345_);
    return v___x_346_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__1() -> *mut LeanObject {
    let mut v_range_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v_range_347_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_348_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__0_once),
        _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__0,
    );
    v___x_349_ = lean_int_emod(v___x_348_, v_range_347_);
    return v___x_349_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__2() -> *mut LeanObject {
    let mut v_range_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v_range_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__1_once),
        _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__1,
    );
    v___x_352_ = lean_int_add(v___x_351_, v_range_350_);
    return v___x_352_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__3() -> *mut LeanObject {
    let mut v_range_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v_range_353_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4_once),
        _init_l_Std_Time_Minute_instOfNatOrdinal___aux__1___closed__4,
    );
    v___x_354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__2_once),
        _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__2,
    );
    v___x_355_ = lean_int_emod(v___x_354_, v_range_353_);
    return v___x_355_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__4() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__3_once),
        _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__3,
    );
    v___x_358_ = lean_int_add(v___x_357_, v___x_356_);
    return v___x_358_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOrdinal() -> *mut LeanObject {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v___x_359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOrdinal___closed__4_once),
        _init_l_Std_Time_Minute_instInhabitedOrdinal___closed__4,
    );
    return v___x_359_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOrdinal___aux__1(
    mut v_x_360_: *mut LeanObject,
    mut v_y_361_: *mut LeanObject,
) -> u8 {
    let mut v___x_362_: u8 = 0;
    v___x_362_ = lean_int_dec_le(v_x_360_, v_y_361_);
    return v___x_362_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOrdinal___aux__1___boxed(
    mut v_x_363_: *mut LeanObject,
    mut v_y_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_365_: u8 = 0;
    let mut v_r_366_: *mut LeanObject = core::ptr::null_mut();
    v_res_365_ = l_Std_Time_Minute_instDecidableLeOrdinal___aux__1(v_x_363_, v_y_364_);
    lean_dec(v_y_364_);
    lean_dec(v_x_363_);
    v_r_366_ = lean_box((v_res_365_) as usize);
    return v_r_366_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOrdinal(
    mut v___y_367_: *mut LeanObject,
    mut v___y_368_: *mut LeanObject,
) -> u8 {
    let mut v___x_369_: u8 = 0;
    v___x_369_ = lean_int_dec_le(v___y_367_, v___y_368_);
    return v___x_369_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOrdinal___boxed(
    mut v___y_370_: *mut LeanObject,
    mut v___y_371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_372_: u8 = 0;
    let mut v_r_373_: *mut LeanObject = core::ptr::null_mut();
    v_res_372_ = l_Std_Time_Minute_instDecidableLeOrdinal(v___y_370_, v___y_371_);
    lean_dec(v___y_371_);
    lean_dec(v___y_370_);
    v_r_373_ = lean_box((v_res_372_) as usize);
    return v_r_373_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOrdinal___aux__1(
    mut v_x_374_: *mut LeanObject,
    mut v_y_375_: *mut LeanObject,
) -> u8 {
    let mut v___x_376_: u8 = 0;
    v___x_376_ = lean_int_dec_lt(v_x_374_, v_y_375_);
    return v___x_376_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOrdinal___aux__1___boxed(
    mut v_x_377_: *mut LeanObject,
    mut v_y_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_379_: u8 = 0;
    let mut v_r_380_: *mut LeanObject = core::ptr::null_mut();
    v_res_379_ = l_Std_Time_Minute_instDecidableLtOrdinal___aux__1(v_x_377_, v_y_378_);
    lean_dec(v_y_378_);
    lean_dec(v_x_377_);
    v_r_380_ = lean_box((v_res_379_) as usize);
    return v_r_380_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOrdinal(
    mut v___y_381_: *mut LeanObject,
    mut v___y_382_: *mut LeanObject,
) -> u8 {
    let mut v___x_383_: u8 = 0;
    v___x_383_ = lean_int_dec_lt(v___y_381_, v___y_382_);
    return v___x_383_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOrdinal___boxed(
    mut v___y_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_386_: u8 = 0;
    let mut v_r_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Std_Time_Minute_instDecidableLtOrdinal(v___y_384_, v___y_385_);
    lean_dec(v___y_385_);
    lean_dec(v___y_384_);
    v_r_387_ = lean_box((v_res_386_) as usize);
    return v_r_387_;
}
pub unsafe fn l_Std_Time_Minute_instOrdOrdinal___aux__1(
    mut v_x_388_: *mut LeanObject,
    mut v_y_389_: *mut LeanObject,
) -> u8 {
    let mut v___x_390_: u8 = 0;
    v___x_390_ = lean_int_dec_lt(v_x_388_, v_y_389_);
    if v___x_390_ == 0 {
        let mut v___x_391_: u8 = 0;
        v___x_391_ = lean_int_dec_eq(v_x_388_, v_y_389_);
        if v___x_391_ == 0 {
            let mut v___x_392_: u8 = 0;
            v___x_392_ = 2;
            return v___x_392_;
        } else {
            let mut v___x_393_: u8 = 0;
            v___x_393_ = 1;
            return v___x_393_;
        }
    } else {
        let mut v___x_394_: u8 = 0;
        v___x_394_ = 0;
        return v___x_394_;
    }
}
pub unsafe fn l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed(
    mut v_x_395_: *mut LeanObject,
    mut v_y_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_397_: u8 = 0;
    let mut v_r_398_: *mut LeanObject = core::ptr::null_mut();
    v_res_397_ = l_Std_Time_Minute_instOrdOrdinal___aux__1(v_x_395_, v_y_396_);
    lean_dec(v_y_396_);
    lean_dec(v_x_395_);
    v_r_398_ = lean_box((v_res_397_) as usize);
    return v_r_398_;
}
pub unsafe fn l_Std_Time_Minute_instReprOffset___aux__1(
    mut v_x_401_: *mut LeanObject,
    mut v_p_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: u8 = 0;
    v___x_403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instReprOrdinal___aux__1___closed__0,
    );
    v___x_404_ = lean_int_dec_lt(v_x_401_, v___x_403_);
    if v___x_404_ == 0 {
        let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
        v___x_405_ = l_Int_repr(v_x_401_);
        v___x_406_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_406_, 0, v___x_405_);
        return v___x_406_;
    } else {
        let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
        v___x_407_ = l_Int_repr(v_x_401_);
        v___x_408_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_408_, 0, v___x_407_);
        v___x_409_ = l_Repr_addAppParen(v___x_408_, v_p_402_);
        return v___x_409_;
    }
}
pub unsafe fn l_Std_Time_Minute_instReprOffset___aux__1___boxed(
    mut v_x_410_: *mut LeanObject,
    mut v_p_411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_412_: *mut LeanObject = core::ptr::null_mut();
    v_res_412_ = l_Std_Time_Minute_instReprOffset___aux__1(v_x_410_, v_p_411_);
    lean_dec(v_p_411_);
    lean_dec(v_x_410_);
    return v_res_412_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOffset___aux__1(
    mut v_a_414_: *mut LeanObject,
    mut v_b_415_: *mut LeanObject,
) -> u8 {
    let mut v___x_416_: u8 = 0;
    v___x_416_ = lean_int_dec_eq(v_a_414_, v_b_415_);
    return v___x_416_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOffset___aux__1___boxed(
    mut v_a_417_: *mut LeanObject,
    mut v_b_418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_419_: u8 = 0;
    let mut v_r_420_: *mut LeanObject = core::ptr::null_mut();
    v_res_419_ = l_Std_Time_Minute_instDecidableEqOffset___aux__1(v_a_417_, v_b_418_);
    lean_dec(v_b_418_);
    lean_dec(v_a_417_);
    v_r_420_ = lean_box((v_res_419_) as usize);
    return v_r_420_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Minute_instDecidableEqOffset___aux__1_spec__0_spec__0(
    mut v_a_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = lean_nat_to_int(v_a_421_);
    return v___x_422_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Minute_instDecidableEqOffset___aux__1_spec__0(
    mut v_a_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    v___x_424_ = lean_nat_to_int(v_a_423_);
    v___x_425_ = l_Rat_ofInt(v___x_424_);
    return v___x_425_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOffset(
    mut v_a_426_: *mut LeanObject,
    mut v_b_427_: *mut LeanObject,
) -> u8 {
    let mut v___x_428_: u8 = 0;
    v___x_428_ = lean_int_dec_eq(v_a_426_, v_b_427_);
    return v___x_428_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableEqOffset___boxed(
    mut v_a_429_: *mut LeanObject,
    mut v_b_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_431_: u8 = 0;
    let mut v_r_432_: *mut LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Std_Time_Minute_instDecidableEqOffset(v_a_429_, v_b_430_);
    lean_dec(v_b_430_);
    lean_dec(v_a_429_);
    v_r_432_ = lean_box((v_res_431_) as usize);
    return v_r_432_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__0() -> *mut LeanObject
{
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_unsigned_to_nat(60);
    v___x_434_ = l_Rat_instNatCast___lam__0(v___x_433_);
    return v___x_434_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__1() -> *mut LeanObject
{
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__0_once),
        _init_l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__0,
    );
    v___x_436_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_435_);
    return v___x_436_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOffset___aux__1() -> *mut LeanObject {
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    v___x_437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__1_once),
        _init_l_Std_Time_Minute_instInhabitedOffset___aux__1___closed__1,
    );
    return v___x_437_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOffset___closed__0() -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_unsigned_to_nat(60);
    v___x_439_ =
        l_Nat_cast___at___00Std_Time_Minute_instDecidableEqOffset___aux__1_spec__0(v___x_438_);
    return v___x_439_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOffset___closed__1() -> *mut LeanObject {
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___x_440_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___closed__0_once),
        _init_l_Std_Time_Minute_instInhabitedOffset___closed__0,
    );
    v___x_441_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v___x_440_);
    return v___x_441_;
}
pub unsafe fn _init_l_Std_Time_Minute_instInhabitedOffset() -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Minute_instInhabitedOffset___closed__1_once),
        _init_l_Std_Time_Minute_instInhabitedOffset___closed__1,
    );
    return v___x_442_;
}
pub unsafe fn l_Std_Time_Minute_instAddOffset___aux__1(
    mut v_u1_443_: *mut LeanObject,
    mut v_u2_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_int_add(v_u1_443_, v_u2_444_);
    return v___x_445_;
}
pub unsafe fn l_Std_Time_Minute_instAddOffset___aux__1___boxed(
    mut v_u1_446_: *mut LeanObject,
    mut v_u2_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_448_: *mut LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Std_Time_Minute_instAddOffset___aux__1(v_u1_446_, v_u2_447_);
    lean_dec(v_u2_447_);
    lean_dec(v_u1_446_);
    return v_res_448_;
}
pub unsafe fn l_Std_Time_Minute_instSubOffset___aux__1(
    mut v_u1_451_: *mut LeanObject,
    mut v_u2_452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ = lean_int_sub(v_u1_451_, v_u2_452_);
    return v___x_453_;
}
pub unsafe fn l_Std_Time_Minute_instSubOffset___aux__1___boxed(
    mut v_u1_454_: *mut LeanObject,
    mut v_u2_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Std_Time_Minute_instSubOffset___aux__1(v_u1_454_, v_u2_455_);
    lean_dec(v_u2_455_);
    lean_dec(v_u1_454_);
    return v_res_456_;
}
pub unsafe fn l_Std_Time_Minute_instNegOffset___aux__1(
    mut v_x_459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v___x_460_ = lean_int_neg(v_x_459_);
    return v___x_460_;
}
pub unsafe fn l_Std_Time_Minute_instNegOffset___aux__1___boxed(
    mut v_x_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Std_Time_Minute_instNegOffset___aux__1(v_x_461_);
    lean_dec(v_x_461_);
    return v_res_462_;
}
pub unsafe fn l_Std_Time_Minute_instToStringOffset___aux__1(
    mut v_n_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = l_Int_repr(v_n_465_);
    return v___x_466_;
}
pub unsafe fn l_Std_Time_Minute_instToStringOffset___aux__1___boxed(
    mut v_n_467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_468_: *mut LeanObject = core::ptr::null_mut();
    v_res_468_ = l_Std_Time_Minute_instToStringOffset___aux__1(v_n_467_);
    lean_dec(v_n_467_);
    return v_res_468_;
}
pub unsafe fn _init_l_Std_Time_Minute_instLTOffset() -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = lean_box(0);
    return v___x_471_;
}
pub unsafe fn _init_l_Std_Time_Minute_instLEOffset() -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = lean_box(0);
    return v___x_472_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOffset___aux__1(
    mut v_x_473_: *mut LeanObject,
    mut v_y_474_: *mut LeanObject,
) -> u8 {
    let mut v___x_475_: u8 = 0;
    v___x_475_ = lean_int_dec_le(v_x_473_, v_y_474_);
    return v___x_475_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOffset___aux__1___boxed(
    mut v_x_476_: *mut LeanObject,
    mut v_y_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: u8 = 0;
    let mut v_r_479_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Time_Minute_instDecidableLeOffset___aux__1(v_x_476_, v_y_477_);
    lean_dec(v_y_477_);
    lean_dec(v_x_476_);
    v_r_479_ = lean_box((v_res_478_) as usize);
    return v_r_479_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOffset(
    mut v___y_480_: *mut LeanObject,
    mut v___y_481_: *mut LeanObject,
) -> u8 {
    let mut v___x_482_: u8 = 0;
    v___x_482_ = lean_int_dec_le(v___y_480_, v___y_481_);
    return v___x_482_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLeOffset___boxed(
    mut v___y_483_: *mut LeanObject,
    mut v___y_484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_485_: u8 = 0;
    let mut v_r_486_: *mut LeanObject = core::ptr::null_mut();
    v_res_485_ = l_Std_Time_Minute_instDecidableLeOffset(v___y_483_, v___y_484_);
    lean_dec(v___y_484_);
    lean_dec(v___y_483_);
    v_r_486_ = lean_box((v_res_485_) as usize);
    return v_r_486_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOffset___aux__1(
    mut v_x_487_: *mut LeanObject,
    mut v_y_488_: *mut LeanObject,
) -> u8 {
    let mut v___x_489_: u8 = 0;
    v___x_489_ = lean_int_dec_lt(v_x_487_, v_y_488_);
    return v___x_489_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOffset___aux__1___boxed(
    mut v_x_490_: *mut LeanObject,
    mut v_y_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_492_: u8 = 0;
    let mut v_r_493_: *mut LeanObject = core::ptr::null_mut();
    v_res_492_ = l_Std_Time_Minute_instDecidableLtOffset___aux__1(v_x_490_, v_y_491_);
    lean_dec(v_y_491_);
    lean_dec(v_x_490_);
    v_r_493_ = lean_box((v_res_492_) as usize);
    return v_r_493_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOffset(
    mut v___y_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
) -> u8 {
    let mut v___x_496_: u8 = 0;
    v___x_496_ = lean_int_dec_lt(v___y_494_, v___y_495_);
    return v___x_496_;
}
pub unsafe fn l_Std_Time_Minute_instDecidableLtOffset___boxed(
    mut v___y_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: u8 = 0;
    let mut v_r_500_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Std_Time_Minute_instDecidableLtOffset(v___y_497_, v___y_498_);
    lean_dec(v___y_498_);
    lean_dec(v___y_497_);
    v_r_500_ = lean_box((v_res_499_) as usize);
    return v_r_500_;
}
pub unsafe fn l_Std_Time_Minute_instOfNatOffset(mut v_n_501_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_502_ = lean_nat_to_int(v_n_501_);
    return v___x_502_;
}
pub unsafe fn l_Std_Time_Minute_instOrdOffset___aux__1(
    mut v_x_503_: *mut LeanObject,
    mut v_y_504_: *mut LeanObject,
) -> u8 {
    let mut v___x_505_: u8 = 0;
    v___x_505_ = lean_int_dec_lt(v_x_503_, v_y_504_);
    if v___x_505_ == 0 {
        let mut v___x_506_: u8 = 0;
        v___x_506_ = lean_int_dec_eq(v_x_503_, v_y_504_);
        if v___x_506_ == 0 {
            let mut v___x_507_: u8 = 0;
            v___x_507_ = 2;
            return v___x_507_;
        } else {
            let mut v___x_508_: u8 = 0;
            v___x_508_ = 1;
            return v___x_508_;
        }
    } else {
        let mut v___x_509_: u8 = 0;
        v___x_509_ = 0;
        return v___x_509_;
    }
}
pub unsafe fn l_Std_Time_Minute_instOrdOffset___aux__1___boxed(
    mut v_x_510_: *mut LeanObject,
    mut v_y_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_512_: u8 = 0;
    let mut v_r_513_: *mut LeanObject = core::ptr::null_mut();
    v_res_512_ = l_Std_Time_Minute_instOrdOffset___aux__1(v_x_510_, v_y_511_);
    lean_dec(v_y_511_);
    lean_dec(v_x_510_);
    v_r_513_ = lean_box((v_res_512_) as usize);
    return v_r_513_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofInt___redArg(
    mut v_data_516_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_516_);
    return v_data_516_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofInt___redArg___boxed(
    mut v_data_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_518_: *mut LeanObject = core::ptr::null_mut();
    v_res_518_ = l_Std_Time_Minute_Ordinal_ofInt___redArg(v_data_517_);
    lean_dec(v_data_517_);
    return v_res_518_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofInt(
    mut v_data_519_: *mut LeanObject,
    mut v_h_520_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_data_519_);
    return v_data_519_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofInt___boxed(
    mut v_data_521_: *mut LeanObject,
    mut v_h_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_523_: *mut LeanObject = core::ptr::null_mut();
    v_res_523_ = l_Std_Time_Minute_Ordinal_ofInt(v_data_521_, v_h_522_);
    lean_dec(v_data_521_);
    return v_res_523_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofNat___redArg(
    mut v_data_524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    v___x_525_ = lean_nat_to_int(v_data_524_);
    return v___x_525_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofNat(
    mut v_data_526_: *mut LeanObject,
    mut v_h_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = lean_nat_to_int(v_data_526_);
    return v___x_528_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_ofFin(mut v_data_529_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    v___x_530_ = lean_nat_to_int(v_data_529_);
    return v___x_530_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_toOffset(
    mut v_ordinal_531_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ordinal_531_);
    return v_ordinal_531_;
}
pub unsafe fn l_Std_Time_Minute_Ordinal_toOffset___boxed(
    mut v_ordinal_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_533_: *mut LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Std_Time_Minute_Ordinal_toOffset(v_ordinal_532_);
    lean_dec(v_ordinal_532_);
    return v_res_533_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofNat(mut v_data_534_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    v___x_535_ = lean_nat_to_int(v_data_534_);
    return v___x_535_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofInt(mut v_data_536_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_data_536_);
    return v_data_536_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofInt___boxed(
    mut v_data_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_538_: *mut LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Std_Time_Minute_Offset_ofInt(v_data_537_);
    lean_dec(v_data_537_);
    return v_res_538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Minute(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Second(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_Minute_instLEOrdinal = _init_l_Std_Time_Minute_instLEOrdinal();
    lean_mark_persistent(l_Std_Time_Minute_instLEOrdinal);
    l_Std_Time_Minute_instLTOrdinal = _init_l_Std_Time_Minute_instLTOrdinal();
    lean_mark_persistent(l_Std_Time_Minute_instLTOrdinal);
    l_Std_Time_Minute_instInhabitedOrdinal = _init_l_Std_Time_Minute_instInhabitedOrdinal();
    lean_mark_persistent(l_Std_Time_Minute_instInhabitedOrdinal);
    l_Std_Time_Minute_instInhabitedOffset___aux__1 =
        _init_l_Std_Time_Minute_instInhabitedOffset___aux__1();
    lean_mark_persistent(l_Std_Time_Minute_instInhabitedOffset___aux__1);
    l_Std_Time_Minute_instInhabitedOffset = _init_l_Std_Time_Minute_instInhabitedOffset();
    lean_mark_persistent(l_Std_Time_Minute_instInhabitedOffset);
    l_Std_Time_Minute_instLTOffset = _init_l_Std_Time_Minute_instLTOffset();
    lean_mark_persistent(l_Std_Time_Minute_instLTOffset);
    l_Std_Time_Minute_instLEOffset = _init_l_Std_Time_Minute_instLEOffset();
    lean_mark_persistent(l_Std_Time_Minute_instLEOffset);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Minute(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_Unit_Minute(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Second(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Minute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Minute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Minute(builtin);
}
