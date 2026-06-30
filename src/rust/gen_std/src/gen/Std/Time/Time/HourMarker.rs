// Lean compiler output
// Module: Std.Time.Time.HourMarker
// Imports: Std.Time.Time.Basic
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_emod, lean_int_neg,
    lean_int_sub, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Time::Basic::{
    initialize_Std_Time_Time_Basic, runtime_initialize_Std_Time_Time_Basic,
};
pub static l_Std_Time_instReprHourMarker_repr___closed__0_value: leanh::LeanStringObject<
    23,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprHourMarker_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprHourMarker_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprHourMarker_repr___closed__2_value: leanh::LeanStringObject<
    23,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprHourMarker_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprHourMarker_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker_repr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprHourMarker_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprHourMarker_repr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprHourMarker_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprHourMarker___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprHourMarker_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprHourMarker___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instReprHourMarker: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprHourMarker___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instOrdHourMarker___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdHourMarker___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdHourMarker___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdHourMarker___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instOrdHourMarker: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdHourMarker___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_HourMarker_ofOrdinal___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_ofOrdinal___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toAbsolute___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toAbsolute___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toRelative___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toRelative___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_HourMarker_toRelative___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_HourMarker_toRelative___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_HourMarker_toRelative___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_HourMarker_toRelative___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_HourMarker_toRelative___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toRelative___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_HourMarker_toRelative___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_HourMarker_toRelative___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Time_HourMarker_ctorIdx(mut v_x_257_: u8) -> *mut leanh::LeanObject {
    if v_x_257_ == 0 {
        let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_258_ = leanh::lean_unsigned_to_nat(0);
        return v___x_258_;
    } else {
        let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_259_ = leanh::lean_unsigned_to_nat(1);
        return v___x_259_;
    }
}
pub unsafe fn l_Std_Time_HourMarker_ctorIdx___boxed(
    mut v_x_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_261_: u8 = 0;
    let mut v_res_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_261_ = (leanh::lean_unbox(v_x_260_) as u8);
    v_res_262_ = l_Std_Time_HourMarker_ctorIdx(v_x_boxed_261_);
    return v_res_262_;
}
pub unsafe fn l_Std_Time_HourMarker_toCtorIdx(mut v_x_263_: u8) -> *mut leanh::LeanObject {
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_264_ = l_Std_Time_HourMarker_ctorIdx(v_x_263_);
    return v___x_264_;
}
pub unsafe fn l_Std_Time_HourMarker_toCtorIdx___boxed(
    mut v_x_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_266_: u8 = 0;
    let mut v_res_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_266_ = (leanh::lean_unbox(v_x_265_) as u8);
    v_res_267_ = l_Std_Time_HourMarker_toCtorIdx(v_x_4__boxed_266_);
    return v_res_267_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim___redArg(
    mut v_k_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_268_);
    return v_k_268_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim___redArg___boxed(
    mut v_k_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_270_ = l_Std_Time_HourMarker_ctorElim___redArg(v_k_269_);
    leanh::lean_dec(v_k_269_);
    return v_res_270_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim(
    mut v_motive_271_: *mut leanh::LeanObject,
    mut v_ctorIdx_272_: *mut leanh::LeanObject,
    mut v_t_273_: u8,
    mut v_h_274_: *mut leanh::LeanObject,
    mut v_k_275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_275_);
    return v_k_275_;
}
pub unsafe fn l_Std_Time_HourMarker_ctorElim___boxed(
    mut v_motive_276_: *mut leanh::LeanObject,
    mut v_ctorIdx_277_: *mut leanh::LeanObject,
    mut v_t_278_: *mut leanh::LeanObject,
    mut v_h_279_: *mut leanh::LeanObject,
    mut v_k_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_281_: u8 = 0;
    let mut v_res_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_281_ = (leanh::lean_unbox(v_t_278_) as u8);
    v_res_282_ = l_Std_Time_HourMarker_ctorElim(
        v_motive_276_,
        v_ctorIdx_277_,
        v_t_boxed_281_,
        v_h_279_,
        v_k_280_,
    );
    leanh::lean_dec(v_k_280_);
    leanh::lean_dec(v_ctorIdx_277_);
    return v_res_282_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim___redArg(
    mut v_am_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_am_283_);
    return v_am_283_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim___redArg___boxed(
    mut v_am_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ = l_Std_Time_HourMarker_am_elim___redArg(v_am_284_);
    leanh::lean_dec(v_am_284_);
    return v_res_285_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim(
    mut v_motive_286_: *mut leanh::LeanObject,
    mut v_t_287_: u8,
    mut v_h_288_: *mut leanh::LeanObject,
    mut v_am_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_am_289_);
    return v_am_289_;
}
pub unsafe fn l_Std_Time_HourMarker_am_elim___boxed(
    mut v_motive_290_: *mut leanh::LeanObject,
    mut v_t_291_: *mut leanh::LeanObject,
    mut v_h_292_: *mut leanh::LeanObject,
    mut v_am_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_294_: u8 = 0;
    let mut v_res_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_294_ = (leanh::lean_unbox(v_t_291_) as u8);
    v_res_295_ = l_Std_Time_HourMarker_am_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_am_293_);
    leanh::lean_dec(v_am_293_);
    return v_res_295_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim___redArg(
    mut v_pm_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_pm_296_);
    return v_pm_296_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim___redArg___boxed(
    mut v_pm_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Std_Time_HourMarker_pm_elim___redArg(v_pm_297_);
    leanh::lean_dec(v_pm_297_);
    return v_res_298_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim(
    mut v_motive_299_: *mut leanh::LeanObject,
    mut v_t_300_: u8,
    mut v_h_301_: *mut leanh::LeanObject,
    mut v_pm_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_pm_302_);
    return v_pm_302_;
}
pub unsafe fn l_Std_Time_HourMarker_pm_elim___boxed(
    mut v_motive_303_: *mut leanh::LeanObject,
    mut v_t_304_: *mut leanh::LeanObject,
    mut v_h_305_: *mut leanh::LeanObject,
    mut v_pm_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_307_: u8 = 0;
    let mut v_res_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_307_ = (leanh::lean_unbox(v_t_304_) as u8);
    v_res_308_ = l_Std_Time_HourMarker_pm_elim(v_motive_303_, v_t_boxed_307_, v_h_305_, v_pm_306_);
    leanh::lean_dec(v_pm_306_);
    return v_res_308_;
}
pub unsafe fn _init_l_Std_Time_instReprHourMarker_repr___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = leanh::lean_unsigned_to_nat(2);
    v___x_316_ = lean_nat_to_int(v___x_315_);
    return v___x_316_;
}
pub unsafe fn _init_l_Std_Time_instReprHourMarker_repr___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = leanh::lean_unsigned_to_nat(1);
    v___x_318_ = lean_nat_to_int(v___x_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_Time_instReprHourMarker_repr(
    mut v_x_319_: u8,
    mut v_prec_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: u8 = 0;
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u8 = 0;
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_319_ == 0 {
                    v___x_335_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_336_ = lean_nat_dec_le(v___x_335_, v_prec_320_);
                    if v___x_336_ == 0 {
                        v___x_337_ = leanh::lean_obj_once(
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
                        v___x_338_ = leanh::lean_obj_once(
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
                    v___x_339_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_340_ = lean_nat_dec_le(v___x_339_, v_prec_320_);
                    if v___x_340_ == 0 {
                        v___x_341_ = leanh::lean_obj_once(
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
                        v___x_342_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_322_);
                v___x_324_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_324_, 0, v___y_322_);
                leanh::lean_ctor_set(v___x_324_, 1, v___x_323_);
                v___x_325_ = 0;
                v___x_326_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_326_, 0, v___x_324_);
                leanh::lean_ctor_set_uint8(
                    v___x_326_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_325_,
                );
                v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_320_);
                return v___x_327_;
            }
            2 => {
                v___x_330_ = l_Std_Time_instReprHourMarker_repr___closed__3;
                leanh::lean_inc(v___y_329_);
                v___x_331_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_331_, 0, v___y_329_);
                leanh::lean_ctor_set(v___x_331_, 1, v___x_330_);
                v___x_332_ = 0;
                v___x_333_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_333_, 0, v___x_331_);
                leanh::lean_ctor_set_uint8(
                    v___x_333_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_343_: *mut leanh::LeanObject,
    mut v_prec_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_121__boxed_345_: u8 = 0;
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_121__boxed_345_ = (leanh::lean_unbox(v_x_343_) as u8);
    v_res_346_ = l_Std_Time_instReprHourMarker_repr(v_x_121__boxed_345_, v_prec_344_);
    leanh::lean_dec(v_prec_344_);
    return v_res_346_;
}
pub unsafe fn l_Std_Time_HourMarker_ofNat(mut v_n_349_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: u8 = 0;
    v___x_350_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_n_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_355_: u8 = 0;
    let mut v_r_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_355_ = l_Std_Time_HourMarker_ofNat(v_n_354_);
    leanh::lean_dec(v_n_354_);
    v_r_356_ = leanh::lean_box((v_res_355_) as usize);
    return v_r_356_;
}
pub unsafe fn l_Std_Time_instDecidableEqHourMarker(mut v_x_357_: u8, mut v_y_358_: u8) -> u8 {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    v___x_359_ = l_Std_Time_HourMarker_ctorIdx(v_x_357_);
    v___x_360_ = l_Std_Time_HourMarker_ctorIdx(v_y_358_);
    v___x_361_ = lean_nat_dec_eq(v___x_359_, v___x_360_);
    leanh::lean_dec(v___x_360_);
    leanh::lean_dec(v___x_359_);
    return v___x_361_;
}
pub unsafe fn l_Std_Time_instDecidableEqHourMarker___boxed(
    mut v_x_362_: *mut leanh::LeanObject,
    mut v_y_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13__boxed_364_: u8 = 0;
    let mut v_y_14__boxed_365_: u8 = 0;
    let mut v_res_366_: u8 = 0;
    let mut v_r_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_364_ = (leanh::lean_unbox(v_x_362_) as u8);
    v_y_14__boxed_365_ = (leanh::lean_unbox(v_y_363_) as u8);
    v_res_366_ = l_Std_Time_instDecidableEqHourMarker(v_x_13__boxed_364_, v_y_14__boxed_365_);
    v_r_367_ = leanh::lean_box((v_res_366_) as usize);
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
    mut v_x_374_: *mut leanh::LeanObject,
    mut v_x_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_40__boxed_376_: u8 = 0;
    let mut v_x_41__boxed_377_: u8 = 0;
    let mut v_res_378_: u8 = 0;
    let mut v_r_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_40__boxed_376_ = (leanh::lean_unbox(v_x_374_) as u8);
    v_x_41__boxed_377_ = (leanh::lean_unbox(v_x_375_) as u8);
    v_res_378_ = l_Std_Time_instOrdHourMarker___lam__0(v_x_40__boxed_376_, v_x_41__boxed_377_);
    v_r_379_ = leanh::lean_box((v_res_378_) as usize);
    return v_r_379_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_ofOrdinal___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = leanh::lean_unsigned_to_nat(12);
    v___x_383_ = lean_nat_to_int(v___x_382_);
    return v___x_383_;
}
pub unsafe fn l_Std_Time_HourMarker_ofOrdinal(
    mut v_time_384_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: u8 = 0;
    v___x_385_ = leanh::lean_obj_once(
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
    mut v_time_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_390_: u8 = 0;
    let mut v_r_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Std_Time_HourMarker_ofOrdinal(v_time_389_);
    leanh::lean_dec(v_time_389_);
    v_r_391_ = leanh::lean_box((v_res_390_) as usize);
    return v_r_391_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_HourMarker_toAbsolute_spec__0(
    mut v_a_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = lean_nat_to_int(v_a_392_);
    return v___x_393_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = leanh::lean_unsigned_to_nat(0);
    v___x_395_ = lean_nat_to_int(v___x_394_);
    return v___x_395_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = leanh::lean_unsigned_to_nat(23);
    v___x_397_ = lean_nat_to_int(v___x_396_);
    return v___x_397_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__1_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__1,
    );
    v___x_399_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_400_ = lean_int_add(v___x_399_, v___x_398_);
    return v___x_400_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_402_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__2_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__2,
    );
    v___x_403_ = lean_int_sub(v___x_402_, v___x_401_);
    return v___x_403_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instReprHourMarker_repr___closed__5_once),
        _init_l_Std_Time_instReprHourMarker_repr___closed__5,
    );
    v___x_405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__3_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__3,
    );
    v_range_406_ = lean_int_add(v___x_405_, v___x_404_);
    return v_range_406_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_408_ = lean_int_sub(v___x_407_, v___x_407_);
    return v___x_408_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__6() -> *mut leanh::LeanObject
{
    let mut v_range_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_409_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_410_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__5_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__5,
    );
    v___x_411_ = lean_int_emod(v___x_410_, v_range_409_);
    return v___x_411_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__7() -> *mut leanh::LeanObject
{
    let mut v_range_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_412_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__6_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__6,
    );
    v___x_414_ = lean_int_add(v___x_413_, v_range_412_);
    return v___x_414_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__8() -> *mut leanh::LeanObject
{
    let mut v_range_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_415_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_416_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__7_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__7,
    );
    v___x_417_ = lean_int_emod(v___x_416_, v_range_415_);
    return v___x_417_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_419_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__8_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__8,
    );
    v___x_420_ = lean_int_add(v___x_419_, v___x_418_);
    return v___x_420_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__10() -> *mut leanh::LeanObject
{
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ = leanh::lean_unsigned_to_nat(24);
    v___x_422_ = lean_nat_to_int(v___x_421_);
    return v___x_422_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_424_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_425_ = lean_int_sub(v___x_424_, v___x_423_);
    return v___x_425_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__12() -> *mut leanh::LeanObject
{
    let mut v_range_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_426_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_427_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__11_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__11,
    );
    v___x_428_ = lean_int_emod(v___x_427_, v_range_426_);
    return v___x_428_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__13() -> *mut leanh::LeanObject
{
    let mut v_range_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_429_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_430_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__12_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__12,
    );
    v___x_431_ = lean_int_add(v___x_430_, v_range_429_);
    return v___x_431_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__14() -> *mut leanh::LeanObject
{
    let mut v_range_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_432_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__4_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__4,
    );
    v___x_433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__13_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__13,
    );
    v___x_434_ = lean_int_emod(v___x_433_, v_range_432_);
    return v___x_434_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toAbsolute___closed__15() -> *mut leanh::LeanObject
{
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_435_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_436_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__14_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__14,
    );
    v___x_437_ = lean_int_add(v___x_436_, v___x_435_);
    return v___x_437_;
}
pub unsafe fn l_Std_Time_HourMarker_toAbsolute(
    mut v_marker_438_: u8,
    mut v_time_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_marker_438_ == 0 {
        let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_441_: u8 = 0;
        v___x_440_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
            _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
        );
        v___x_441_ = lean_int_dec_eq(v_time_439_, v___x_440_);
        if v___x_441_ == 0 {
            leanh::lean_inc(v_time_439_);
            return v_time_439_;
        } else {
            let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_442_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__9),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__9_once),
                _init_l_Std_Time_HourMarker_toAbsolute___closed__9,
            );
            return v___x_442_;
        }
    } else {
        let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_444_: u8 = 0;
        v___x_443_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
            _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
        );
        v___x_444_ = lean_int_dec_eq(v_time_439_, v___x_443_);
        if v___x_444_ == 0 {
            let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_445_ = lean_int_add(v_time_439_, v___x_443_);
            v___x_446_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__10),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__10_once),
                _init_l_Std_Time_HourMarker_toAbsolute___closed__10,
            );
            v___x_447_ = lean_int_emod(v___x_445_, v___x_446_);
            leanh::lean_dec(v___x_445_);
            return v___x_447_;
        } else {
            let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_448_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__15),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__15_once),
                _init_l_Std_Time_HourMarker_toAbsolute___closed__15,
            );
            return v___x_448_;
        }
    }
}
pub unsafe fn l_Std_Time_HourMarker_toAbsolute___boxed(
    mut v_marker_449_: *mut leanh::LeanObject,
    mut v_time_450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_marker_boxed_451_: u8 = 0;
    let mut v_res_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_marker_boxed_451_ = (leanh::lean_unbox(v_marker_449_) as u8);
    v_res_452_ = l_Std_Time_HourMarker_toAbsolute(v_marker_boxed_451_, v_time_450_);
    leanh::lean_dec(v_time_450_);
    return v_res_452_;
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
    mut v___x_453_: *mut leanh::LeanObject,
    mut v_h_u2081_454_: *mut leanh::LeanObject,
    mut v_h_u2082_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    v___x_456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_457_ = lean_int_dec_lt(v___x_453_, v___x_456_);
    if v___x_457_ == 0 {
        let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h_u2081_454_);
        v___x_458_ = leanh::lean_apply_1(v_h_u2082_455_, leanh::lean_box(0));
        return v___x_458_;
    } else {
        let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h_u2082_455_);
        v___x_459_ = leanh::lean_apply_1(v_h_u2081_454_, leanh::lean_box(0));
        return v___x_459_;
    }
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg___boxed(
    mut v___x_460_: *mut leanh::LeanObject,
    mut v_h_u2081_461_: *mut leanh::LeanObject,
    mut v_h_u2082_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
        v___x_460_,
        v_h_u2081_461_,
        v_h_u2082_462_,
    );
    leanh::lean_dec(v___x_460_);
    return v_res_463_;
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0(
    mut v___x_464_: *mut leanh::LeanObject,
    mut v_p_465_: *mut leanh::LeanObject,
    mut v_q_466_: *mut leanh::LeanObject,
    mut v_00_u03b1_467_: *mut leanh::LeanObject,
    mut v_h_468_: *mut leanh::LeanObject,
    mut v_h_u2081_469_: *mut leanh::LeanObject,
    mut v_h_u2082_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
        v___x_464_,
        v_h_u2081_469_,
        v_h_u2082_470_,
    );
    return v___x_471_;
}
pub unsafe fn l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___boxed(
    mut v___x_472_: *mut leanh::LeanObject,
    mut v_p_473_: *mut leanh::LeanObject,
    mut v_q_474_: *mut leanh::LeanObject,
    mut v_00_u03b1_475_: *mut leanh::LeanObject,
    mut v_h_476_: *mut leanh::LeanObject,
    mut v_h_u2081_477_: *mut leanh::LeanObject,
    mut v_h_u2082_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0(
        v___x_472_,
        v_p_473_,
        v_q_474_,
        v_00_u03b1_475_,
        v_h_476_,
        v_h_u2081_477_,
        v_h_u2082_478_,
    );
    leanh::lean_dec(v___x_472_);
    return v_res_479_;
}
pub unsafe fn l_Std_Time_HourMarker_toRelative___lam__0(
    mut v_x_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Std_Time_HourMarker_toRelative___lam__1(
    mut v_hour_481_: *mut leanh::LeanObject,
    mut v_x_482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_483_: u8 = 0;
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = 0;
    v___x_484_ = leanh::lean_box((v___x_483_) as usize);
    v___x_485_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_485_, 0, v_hour_481_);
    leanh::lean_ctor_set(v___x_485_, 1, v___x_484_);
    return v___x_485_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toRelative___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_487_ = lean_int_neg(v___x_486_);
    return v___x_487_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toRelative___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = 1;
    v___x_490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_491_ = leanh::lean_box((v___x_489_) as usize);
    v___x_492_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_492_, 0, v___x_490_);
    leanh::lean_ctor_set(v___x_492_, 1, v___x_491_);
    return v___x_492_;
}
pub unsafe fn _init_l_Std_Time_HourMarker_toRelative___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_493_: u8 = 0;
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = 0;
    v___x_494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
        _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
    );
    v___x_495_ = leanh::lean_box((v___x_493_) as usize);
    v___x_496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_496_, 0, v___x_494_);
    leanh::lean_ctor_set(v___x_496_, 1, v___x_495_);
    return v___x_496_;
}
pub unsafe fn l_Std_Time_HourMarker_toRelative(
    mut v_hour_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: u8 = 0;
    v___x_498_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toAbsolute___closed__0_once),
        _init_l_Std_Time_HourMarker_toAbsolute___closed__0,
    );
    v___x_499_ = lean_int_dec_eq(v_hour_497_, v___x_498_);
    if v___x_499_ == 0 {
        let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_501_: u8 = 0;
        v___x_500_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_HourMarker_ofOrdinal___closed__0_once),
            _init_l_Std_Time_HourMarker_ofOrdinal___closed__0,
        );
        v___x_501_ = lean_int_dec_le(v_hour_497_, v___x_500_);
        if v___x_501_ == 0 {
            let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_504_: u8 = 0;
            let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_502_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__0),
                core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__0_once),
                _init_l_Std_Time_HourMarker_toRelative___closed__0,
            );
            v___x_503_ = lean_int_add(v_hour_497_, v___x_502_);
            leanh::lean_dec(v_hour_497_);
            v___x_504_ = 1;
            v___x_505_ = leanh::lean_box((v___x_504_) as usize);
            v___x_506_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_506_, 0, v___x_503_);
            leanh::lean_ctor_set(v___x_506_, 1, v___x_505_);
            return v___x_506_;
        } else {
            let mut v___x_507_: u8 = 0;
            v___x_507_ = lean_int_dec_eq(v_hour_497_, v___x_500_);
            if v___x_507_ == 0 {
                let mut v___f_508_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_509_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___f_508_ = l_Std_Time_HourMarker_toRelative___closed__1;
                leanh::lean_inc(v_hour_497_);
                v___f_509_ = leanh::lean_alloc_closure(
                    l_Std_Time_HourMarker_toRelative___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_509_, 0, v_hour_497_);
                v___x_510_ =
                    l_Or_by__cases___at___00Std_Time_HourMarker_toRelative_spec__0___redArg(
                        v_hour_497_,
                        v___f_508_,
                        v___f_509_,
                    );
                leanh::lean_dec(v_hour_497_);
                return v___x_510_;
            } else {
                let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_hour_497_);
                v___x_511_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_HourMarker_toRelative___closed__2_once),
                    _init_l_Std_Time_HourMarker_toRelative___closed__2,
                );
                return v___x_511_;
            }
        }
    } else {
        let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_hour_497_);
        v___x_512_ = leanh::lean_obj_once(
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
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_HourMarker(
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
pub unsafe fn initialize_Std_Time_Time_HourMarker(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_HourMarker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_HourMarker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_HourMarker(builtin);
}