// Lean compiler output
// Module: Std.Time.Time.HourMarker
// Imports: Std.Time.Time.Basic
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Time::Basic::{
    initialize_Std_Time_Time_Basic, runtime_initialize_Std_Time_Time_Basic,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_emod;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le};
pub static l_Std_Time_instReprHourMarker_repr___closed__0_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 72, 111, 117, 114, 77, 97, 114, 107, 101, 114, 46,
        97, 109, 0,
    ],
};
static mut l_Std_Time_instReprHourMarker_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprHourMarker_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprHourMarker_repr___closed__2_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 72, 111, 117, 114, 77, 97, 114, 107, 101, 114, 46,
        112, 109, 0,
    ],
};
static mut l_Std_Time_instReprHourMarker_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprHourMarker_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprHourMarker_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprHourMarker_repr___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprHourMarker___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprHourMarker_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprHourMarker___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprHourMarker: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdHourMarker___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdHourMarker___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdHourMarker___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdHourMarker___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instOrdHourMarker: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdHourMarker___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_HourMarker_ofOrdinal___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_ofOrdinal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toRelative___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toRelative___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_HourMarker_toRelative___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_HourMarker_toRelative___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_HourMarker_toRelative___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_HourMarker_toRelative___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_HourMarker_toRelative___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toRelative___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toRelative___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toRelative___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Time_HourMarker_ctorIdx(mut v_x_257_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_257_ == 0 {
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_258_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_258_;
    } else {
        let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_259_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_259_;
    }
}
pub unsafe fn l_Std_Time_HourMarker_ctorIdx___boxed(
    mut v_x_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_261_: u8 = 0;
    let mut v_res_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_261_ = (crate::leanh::lean_unbox(v_x_260_) as u8);
    v_res_262_ = l_Std_Time_HourMarker_ctorIdx(v_x_boxed_261_);
    return v_res_262_;
}
pub unsafe fn l_Std_Time_HourMarker_toCtorIdx(mut v_x_263_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_264_ = l_Std_Time_HourMarker_ctorIdx(v_x_263_);
    return v___x_264_;
}
pub unsafe fn l_Std_Time_HourMarker_toCtorIdx___boxed(
    mut v_x_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_266_: u8 = 0;
    let mut v_res_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_266_ = (crate::leanh::lean_unbox(v_x_265_) as u8);
    v_res_267_ = l_Std_Time_HourMarker_toCtorIdx(v_x_4__boxed_266_);
    return v_res_267_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim___redArg(
    mut v_k_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_268_);
    return v_k_268_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim___redArg___boxed(
    mut v_k_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_270_ = l_Std_Time_HourMarker_ctorElim___redArg(v_k_269_);
    crate::leanh::lean_dec(v_k_269_);
    return v_res_270_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim(
    mut v_motive_271_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_272_: *mut crate::leanh::LeanObject,
    mut v_t_273_: u8,
    mut v_h_274_: *mut crate::leanh::LeanObject,
    mut v_k_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_275_);
    return v_k_275_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim___boxed(
    mut v_motive_276_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_277_: *mut crate::leanh::LeanObject,
    mut v_t_278_: *mut crate::leanh::LeanObject,
    mut v_h_279_: *mut crate::leanh::LeanObject,
    mut v_k_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_281_: u8 = 0;
    let mut v_res_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_281_ = (crate::leanh::lean_unbox(v_t_278_) as u8);
    v_res_282_ = l_Std_Time_HourMarker_ctorElim(
        v_motive_276_,
        v_ctorIdx_277_,
        v_t_boxed_281_,
        v_h_279_,
        v_k_280_,
    );
    crate::leanh::lean_dec(v_k_280_);
    crate::leanh::lean_dec(v_ctorIdx_277_);
    return v_res_282_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim___redArg(
    mut v_am_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_am_283_);
    return v_am_283_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim___redArg___boxed(
    mut v_am_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Std_Time_HourMarker_am_elim___redArg(v_am_284_);
    crate::leanh::lean_dec(v_am_284_);
    return v_res_285_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim(
    mut v_motive_286_: *mut crate::leanh::LeanObject,
    mut v_t_287_: u8,
    mut v_h_288_: *mut crate::leanh::LeanObject,
    mut v_am_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_am_289_);
    return v_am_289_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim___boxed(
    mut v_motive_290_: *mut crate::leanh::LeanObject,
    mut v_t_291_: *mut crate::leanh::LeanObject,
    mut v_h_292_: *mut crate::leanh::LeanObject,
    mut v_am_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_294_: u8 = 0;
    let mut v_res_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_294_ = (crate::leanh::lean_unbox(v_t_291_) as u8);
    v_res_295_ = l_Std_Time_HourMarker_am_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_am_293_);
    crate::leanh::lean_dec(v_am_293_);
    return v_res_295_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim___redArg(
    mut v_pm_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pm_296_);
    return v_pm_296_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim___redArg___boxed(
    mut v_pm_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Std_Time_HourMarker_pm_elim___redArg(v_pm_297_);
    crate::leanh::lean_dec(v_pm_297_);
    return v_res_298_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim(
    mut v_motive_299_: *mut crate::leanh::LeanObject,
    mut v_t_300_: u8,
    mut v_h_301_: *mut crate::leanh::LeanObject,
    mut v_pm_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pm_302_);
    return v_pm_302_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim___boxed(
    mut v_motive_303_: *mut crate::leanh::LeanObject,
    mut v_t_304_: *mut crate::leanh::LeanObject,
    mut v_h_305_: *mut crate::leanh::LeanObject,
    mut v_pm_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_307_: u8 = 0;
    let mut v_res_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_307_ = (crate::leanh::lean_unbox(v_t_304_) as u8);
    v_res_308_ = l_Std_Time_HourMarker_pm_elim(v_motive_303_, v_t_boxed_307_, v_h_305_, v_pm_306_);
    crate::leanh::lean_dec(v_pm_306_);
    return v_res_308_;
}
pub unsafe fn _init_l_Std_Time_instReprHourMarker_repr___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_316_ = lean_nat_to_int(v___x_315_);
    return v___x_316_;
}
pub unsafe fn _init_l_Std_Time_instReprHourMarker_repr___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_318_ = lean_nat_to_int(v___x_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_Time_instReprHourMarker_repr(
    mut v_x_319_: u8,
    mut v_prec_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: u8 = 0;
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u8 = 0;
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_319_ == 0 {
                    v___x_335_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_336_ = lean_nat_dec_le(v___x_335_, v_prec_320_);
                    if v___x_336_ == 0 {
                        v___x_337_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprHourMarker_repr___closed__4_once
                            ),
                            _init_l_Std_Time_instReprHourMarker_repr___closed__4,
                        );
                        v___y_322_ = v___x_337_;
                        state = 1;
                        continue;
                    } else {
                        v___x_338_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprHourMarker_repr___closed__5_once
                            ),
                            _init_l_Std_Time_instReprHourMarker_repr___closed__5,
                        );
                        v___y_322_ = v___x_338_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_339_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_340_ = lean_nat_dec_le(v___x_339_, v_prec_320_);
                    if v___x_340_ == 0 {
                        v___x_341_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprHourMarker_repr___closed__4_once
                            ),
                            _init_l_Std_Time_instReprHourMarker_repr___closed__4,
                        );
                        v___y_329_ = v___x_341_;
                        state = 2;
                        continue;
                    } else {
                        v___x_342_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_instReprHourMarker_repr___closed__5_once
                            ),
                            _init_l_Std_Time_instReprHourMarker_repr___closed__5,
                        );
                        v___y_329_ = v___x_342_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_323_ = l_Std_Time_instReprHourMarker_repr___closed__1;
                crate::leanh::lean_inc(v___y_322_);
                v___x_324_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_324_, 0, v___y_322_);
                crate::leanh::lean_ctor_set(v___x_324_, 1, v___x_323_);
                v___x_325_ = 0;
                v___x_326_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_326_, 0, v___x_324_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_326_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_325_,
                );
                v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_320_);
                return v___x_327_;
            }
            2 => {
                v___x_330_ = l_Std_Time_instReprHourMarker_repr___closed__3;
                crate::leanh::lean_inc(v___y_329_);
                v___x_331_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_331_, 0, v___y_329_);
                crate::leanh::lean_ctor_set(v___x_331_, 1, v___x_330_);
                v___x_332_ = 0;
                v___x_333_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_333_, 0, v___x_331_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_333_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_332_,
                );
                v___x_334_ = l_Repr_addAppParen(v___x_333_, v_prec_320_);
                return v___x_334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprHourMarker_repr___boxed(
    mut v_x_343_: *mut crate::leanh::LeanObject,
    mut v_prec_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_121__boxed_345_: u8 = 0;
    let mut v_res_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_121__boxed_345_ = (crate::leanh::lean_unbox(v_x_343_) as u8);
    v_res_346_ = l_Std_Time_instReprHourMarker_repr(v_x_121__boxed_345_, v_prec_344_);
    crate::leanh::lean_dec(v_prec_344_);
    return v_res_346_;
}
pub unsafe fn l_Std_Time_HourMarker_ofNat(mut v_n_349_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: u8 = 0;
    v___x_350_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_351_ = lean_nat_dec_le(v_n_349_, v___x_350_);
    if v___x_351_ == 0 {
        let mut v___x_352_: u8 = 0;
        v___x_352_ = 1;
        return v___x_352_;
    } else {
        let mut v___x_353_: u8 = 0;
        v___x_353_ = 0;
        return v___x_353_;
    }
}
pub unsafe fn l_Std_Time_HourMarker_ofNat___boxed(
    mut v_n_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_355_: u8 = 0;
    let mut v_r_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_355_ = l_Std_Time_HourMarker_ofNat(v_n_354_);
    crate::leanh::lean_dec(v_n_354_);
    v_r_356_ = crate::leanh::lean_box((v_res_355_) as usize);
    return v_r_356_;
}
pub unsafe fn l_Std_Time_instDecidableEqHourMarker(mut v_x_357_: u8, mut v_y_358_: u8) -> u8 {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    v___x_359_ = l_Std_Time_HourMarker_ctorIdx(v_x_357_);
    v___x_360_ = l_Std_Time_HourMarker_ctorIdx(v_y_358_);
    v___x_361_ = lean_nat_dec_eq(v___x_359_, v___x_360_);
    crate::leanh::lean_dec(v___x_360_);
    crate::leanh::lean_dec(v___x_359_);
    return v___x_361_;
}
pub unsafe fn l_Std_Time_instDecidableEqHourMarker___boxed(
    mut v_x_362_: *mut crate::leanh::LeanObject,
    mut v_y_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_364_: u8 = 0;
    let mut v_y_14__boxed_365_: u8 = 0;
    let mut v_res_366_: u8 = 0;
    let mut v_r_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_364_ = (crate::leanh::lean_unbox(v_x_362_) as u8);
    v_y_14__boxed_365_ = (crate::leanh::lean_unbox(v_y_363_) as u8);
    v_res_366_ = l_Std_Time_instDecidableEqHourMarker(v_x_13__boxed_364_, v_y_14__boxed_365_);
    v_r_367_ = crate::leanh::lean_box((v_res_366_) as usize);
    return v_r_367_;
}
pub unsafe fn l_Std_Time_instOrdHourMarker___lam__0(mut v_x_368_: u8, mut v_x_369_: u8) -> u8 {
    if v_x_368_ == 0 {
        if v_x_369_ == 0 {
            let mut v___x_370_: u8 = 0;
            v___x_370_ = 1;
            return v___x_370_;
        } else {
            let mut v___x_371_: u8 = 0;
            v___x_371_ = 0;
            return v___x_371_;
        }
    } else {
        if v_x_369_ == 0 {
            let mut v___x_372_: u8 = 0;
            v___x_372_ = 2;
            return v___x_372_;
        } else {
            let mut v___x_373_: u8 = 0;
            v___x_373_ = 1;
            return v___x_373_;
        }
    }
}
pub unsafe fn l_Std_Time_instOrdHourMarker___lam__0___boxed(
    mut v_x_374_: *mut crate::leanh::LeanObject,
    mut v_x_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40__boxed_376_: u8 = 0;
    let mut v_x_41__boxed_377_: u8 = 0;
    let mut v_res_378_: u8 = 0;
    let mut v_r_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40__boxed_376_ = (crate::leanh::lean_unbox(v_x_374_) as u8);
    v_x_41__boxed_377_ = (crate::leanh::lean_unbox(v_x_375_) as u8);
    v_res_378_ = l_Std_Time_instOrdHourMarker___lam__0(v_x_40__boxed_376_, v_x_41__boxed_377_);
    v_r_379_ = crate::leanh::lean_box((v_res_378_) as usize);
    return v_r_379_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_ofOrdinal___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_383_ = lean_nat_to_int(v___x_382_);
    return v___x_383_;
}
pub unsafe fn l_Std_Time_HourMarker_ofOrdinal(
    mut v_time_384_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: u8 = 0;
    v___x_385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_386_ = lean_int_dec_le(v___x_385_, v_time_384_);
    if v___x_386_ == 0 {
        let mut v___x_387_: u8 = 0;
        v___x_387_ = 0;
        return v___x_387_;
    } else {
        let mut v___x_388_: u8 = 0;
        v___x_388_ = 1;
        return v___x_388_;
    }
}
pub unsafe fn l_Std_Time_HourMarker_ofOrdinal___boxed(
    mut v_time_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_390_: u8 = 0;
    let mut v_r_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Std_Time_HourMarker_ofOrdinal(v_time_389_);
    crate::leanh::lean_dec(v_time_389_);
    v_r_391_ = crate::leanh::lean_box((v_res_390_) as usize);
    return v_r_391_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_HourMarker_toAbsolute_spec__0(
    mut v_a_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = lean_nat_to_int(v_a_392_);
    return v___x_393_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_395_ = lean_nat_to_int(v___x_394_);
    return v___x_395_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_397_ = lean_nat_to_int(v___x_396_);
    return v___x_397_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__1_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__1,
    );
    v___x_399_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_400_ = lean_int_add(v___x_399_, v___x_398_);
    return v___x_400_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_402_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__2_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__2,
    );
    v___x_403_ = lean_int_sub(v___x_402_, v___x_401_);
    return v___x_403_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__5_once),
        _init_l_Std_Time_instReprHourMarker_repr___closed__5,
    );
    v___x_405_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__3_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__3,
    );
    v_range_406_ = lean_int_add(v___x_405_, v___x_404_);
    return v_range_406_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_408_ = lean_int_sub(v___x_407_, v___x_407_);
    return v___x_408_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v_range_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_409_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_410_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__5_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__5,
    );
    v___x_411_ = lean_int_emod(v___x_410_, v_range_409_);
    return v___x_411_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v_range_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_412_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__6_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__6,
    );
    v___x_414_ = lean_int_add(v___x_413_, v_range_412_);
    return v___x_414_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v_range_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__7_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__7,
    );
    v___x_417_ = lean_int_emod(v___x_416_, v_range_415_);
    return v___x_417_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__8_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__8,
    );
    v___x_420_ = lean_int_add(v___x_419_, v___x_418_);
    return v___x_420_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_422_ = lean_nat_to_int(v___x_421_);
    return v___x_422_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_425_ = lean_int_sub(v___x_424_, v___x_423_);
    return v___x_425_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v_range_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_427_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__11_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__11,
    );
    v___x_428_ = lean_int_emod(v___x_427_, v_range_426_);
    return v___x_428_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v_range_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_429_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__12_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__12,
    );
    v___x_431_ = lean_int_add(v___x_430_, v_range_429_);
    return v___x_431_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v_range_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__13_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__13,
    );
    v___x_434_ = lean_int_emod(v___x_433_, v_range_432_);
    return v___x_434_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_436_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__14_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__14,
    );
    v___x_437_ = lean_int_add(v___x_436_, v___x_435_);
    return v___x_437_;
}
pub unsafe fn l_Std_Time_HourMarker_toAbsolute(
    mut v_marker_438_: u8,
    mut v_time_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_marker_438_ == 0 {
        let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_441_: u8 = 0;
        v___x_440_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
            _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
        );
        v___x_441_ = lean_int_dec_eq(v_time_439_, v___x_440_);
        if v___x_441_ == 0 {
            crate::leanh::lean_inc(v_time_439_);
            return v_time_439_;
        } else {
            let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_442_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__9),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__9_once),
                _init_l_Std_Time_HourMarker_toAbsolute___closed__9,
            );
            return v___x_442_;
        }
    } else {
        let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_444_: u8 = 0;
        v___x_443_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
            _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
        );
        v___x_444_ = lean_int_dec_eq(v_time_439_, v___x_443_);
        if v___x_444_ == 0 {
            let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_445_ = lean_int_add(v_time_439_, v___x_443_);
            v___x_446_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__10),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__10_once),
                _init_l_Std_Time_HourMarker_toAbsolute___closed__10,
            );
            v___x_447_ = lean_int_emod(v___x_445_, v___x_446_);
            crate::leanh::lean_dec(v___x_445_);
            return v___x_447_;
        } else {
            let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_448_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__15),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__15_once),
                _init_l_Std_Time_HourMarker_toAbsolute___closed__15,
            );
            return v___x_448_;
        }
    }
}
pub unsafe fn l_Std_Time_HourMarker_toAbsolute___boxed(
    mut v_marker_449_: *mut crate::leanh::LeanObject,
    mut v_time_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_marker_boxed_451_: u8 = 0;
    let mut v_res_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_marker_boxed_451_ = (crate::leanh::lean_unbox(v_marker_449_) as u8);
    v_res_452_ = l_Std_Time_HourMarker_toAbsolute(v_marker_boxed_451_, v_time_450_);
    crate::leanh::lean_dec(v_time_450_);
    return v_res_452_;
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
    mut v___x_453_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_454_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    v___x_456_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_457_ = lean_int_dec_lt(v___x_453_, v___x_456_);
    if v___x_457_ == 0 {
        let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h_u2081_454_);
        v___x_458_ = crate::leanh::lean_apply_1(v_h_u2082_455_, crate::leanh::lean_box(0));
        return v___x_458_;
    } else {
        let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h_u2082_455_);
        v___x_459_ = crate::leanh::lean_apply_1(v_h_u2081_454_, crate::leanh::lean_box(0));
        return v___x_459_;
    }
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg___boxed(
    mut v___x_460_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_461_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
        v___x_460_,
        v_h_u2081_461_,
        v_h_u2082_462_,
    );
    crate::leanh::lean_dec(v___x_460_);
    return v_res_463_;
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0(
    mut v___x_464_: *mut crate::leanh::LeanObject,
    mut v_p_465_: *mut crate::leanh::LeanObject,
    mut v_q_466_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_467_: *mut crate::leanh::LeanObject,
    mut v_h_468_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_469_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
        v___x_464_,
        v_h_u2081_469_,
        v_h_u2082_470_,
    );
    return v___x_471_;
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___boxed(
    mut v___x_472_: *mut crate::leanh::LeanObject,
    mut v_p_473_: *mut crate::leanh::LeanObject,
    mut v_q_474_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_475_: *mut crate::leanh::LeanObject,
    mut v_h_476_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_477_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0(
        v___x_472_,
        v_p_473_,
        v_q_474_,
        v_00_u03b1_475_,
        v_h_476_,
        v_h_u2081_477_,
        v_h_u2082_478_,
    );
    crate::leanh::lean_dec(v___x_472_);
    return v_res_479_;
}
pub unsafe fn l_Std_Time_HourMarker_toRelative___lam__0(
    mut v_x_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Std_Time_HourMarker_toRelative___lam__1(
    mut v_hour_481_: *mut crate::leanh::LeanObject,
    mut v_x_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: u8 = 0;
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = 0;
    v___x_484_ = crate::leanh::lean_box((v___x_483_) as usize);
    v___x_485_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_485_, 0, v_hour_481_);
    crate::leanh::lean_ctor_set(v___x_485_, 1, v___x_484_);
    return v___x_485_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toRelative___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_487_ = lean_int_neg(v___x_486_);
    return v___x_487_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toRelative___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = 1;
    v___x_490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_491_ = crate::leanh::lean_box((v___x_489_) as usize);
    v___x_492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_492_, 0, v___x_490_);
    crate::leanh::lean_ctor_set(v___x_492_, 1, v___x_491_);
    return v___x_492_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toRelative___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_493_: u8 = 0;
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = 0;
    v___x_494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_495_ = crate::leanh::lean_box((v___x_493_) as usize);
    v___x_496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_496_, 0, v___x_494_);
    crate::leanh::lean_ctor_set(v___x_496_, 1, v___x_495_);
    return v___x_496_;
}
pub unsafe fn l_Std_Time_HourMarker_toRelative(
    mut v_hour_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: u8 = 0;
    v___x_498_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_499_ = lean_int_dec_eq(v_hour_497_, v___x_498_);
    if v___x_499_ == 0 {
        let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_501_: u8 = 0;
        v___x_500_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
            _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
        );
        v___x_501_ = lean_int_dec_le(v_hour_497_, v___x_500_);
        if v___x_501_ == 0 {
            let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_504_: u8 = 0;
            let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_502_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__0),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__0_once),
                _init_l_Std_Time_HourMarker_toRelative___closed__0,
            );
            v___x_503_ = lean_int_add(v_hour_497_, v___x_502_);
            crate::leanh::lean_dec(v_hour_497_);
            v___x_504_ = 1;
            v___x_505_ = crate::leanh::lean_box((v___x_504_) as usize);
            v___x_506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_506_, 0, v___x_503_);
            crate::leanh::lean_ctor_set(v___x_506_, 1, v___x_505_);
            return v___x_506_;
        } else {
            let mut v___x_507_: u8 = 0;
            v___x_507_ = lean_int_dec_eq(v_hour_497_, v___x_500_);
            if v___x_507_ == 0 {
                let mut v___f_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___f_508_ = l_Std_Time_HourMarker_toRelative___closed__1;
                crate::leanh::lean_inc(v_hour_497_);
                v___f_509_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_HourMarker_toRelative___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_509_, 0, v_hour_497_);
                v___x_510_ =
                    l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
                        v_hour_497_,
                        v___f_508_,
                        v___f_509_,
                    );
                crate::leanh::lean_dec(v_hour_497_);
                return v___x_510_;
            } else {
                let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_hour_497_);
                v___x_511_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__2_once),
                    _init_l_Std_Time_HourMarker_toRelative___closed__2,
                );
                return v___x_511_;
            }
        }
    } else {
        let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hour_497_);
        v___x_512_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__3),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__3_once),
            _init_l_Std_Time_HourMarker_toRelative___closed__3,
        );
        return v___x_512_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_HourMarker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_HourMarker(
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
pub unsafe fn initialize_Std_Time_Time_HourMarker(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_HourMarker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_HourMarker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_HourMarker(builtin);
}
