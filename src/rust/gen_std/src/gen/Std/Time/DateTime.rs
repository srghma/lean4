// Lean compiler output
// Module: Std.Time.DateTime
// Imports: Std.Time.Zoned.Offset Std.Time.DateTime.WallTime Std.Time.DateTime.Timestamp Std.Time.DateTime.PlainDateTime Std.Time.Date.Unit.Month
use crate::ffi::{
    lean_int_add, lean_int_div, lean_int_emod, lean_int_mul, lean_int_neg, lean_int_sub,
    lean_nat_to_int,
};
use crate::r#gen::Std::Time::Date::PlainDate::{
    l_Std_Time_PlainDate_ofEpochDay, l_Std_Time_PlainDate_toEpochDay,
};
use crate::r#gen::Std::Time::Date::Unit::Month::{
    initialize_Std_Time_Date_Unit_Month, runtime_initialize_Std_Time_Date_Unit_Month,
};
use crate::r#gen::Std::Time::DateTime::PlainDateTime::{
    initialize_Std_Time_DateTime_PlainDateTime, l_Std_Time_PlainDateTime_toWallTime,
    runtime_initialize_Std_Time_DateTime_PlainDateTime,
};
use crate::r#gen::Std::Time::DateTime::Timestamp::{
    initialize_Std_Time_DateTime_Timestamp, runtime_initialize_Std_Time_DateTime_Timestamp,
};
use crate::r#gen::Std::Time::DateTime::WallTime::{
    initialize_Std_Time_DateTime_WallTime, runtime_initialize_Std_Time_DateTime_WallTime,
};
use crate::r#gen::Std::Time::Duration::l_Std_Time_Duration_ofNanoseconds;
use crate::r#gen::Std::Time::Time::PlainTime::{
    l_Std_Time_PlainTime_midnight, l_Std_Time_PlainTime_ofNanoseconds,
    l_Std_Time_PlainTime_toNanoseconds,
};
use crate::r#gen::Std::Time::Zoned::Offset::{
    initialize_Std_Time_Zoned_Offset, runtime_initialize_Std_Time_Zoned_Offset,
};
static mut l_Std_Time_Timestamp_toWallTime___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_toWallTime___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_toWallTime___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_toWallTime___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_ofWallTime___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_ofWallTime___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_toWallTime___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_toWallTime___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDate_instHSubDuration___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_instHSubDuration___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_instHSubDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instHSubDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_instHSubDuration___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_Timestamp_toWallTime___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_204_ = leanh::lean_unsigned_to_nat(0);
    v___x_205_ = lean_nat_to_int(v___x_204_);
    return v___x_205_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_toWallTime___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_206_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_207_ = lean_nat_to_int(v___x_206_);
    return v___x_207_;
}
pub unsafe fn l_Std_Time_Timestamp_toWallTime(
    mut v_ts_208_: *mut leanh::LeanObject,
    mut v_offset_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_210_ = leanh::lean_ctor_get(v_ts_208_, 0);
    v_nano_211_ = leanh::lean_ctor_get(v_ts_208_, 1);
    v___x_212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_213_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_214_ = lean_int_mul(v_second_210_, v___x_213_);
    v___x_215_ = lean_int_add(v___x_214_, v_nano_211_);
    leanh::lean_dec(v___x_214_);
    v___x_216_ = lean_int_mul(v_offset_209_, v___x_213_);
    v___x_217_ = lean_int_add(v___x_216_, v___x_212_);
    leanh::lean_dec(v___x_216_);
    v___x_218_ = lean_int_add(v___x_215_, v___x_217_);
    leanh::lean_dec(v___x_217_);
    leanh::lean_dec(v___x_215_);
    v___x_219_ = l_Std_Time_Duration_ofNanoseconds(v___x_218_);
    leanh::lean_dec(v___x_218_);
    return v___x_219_;
}
pub unsafe fn l_Std_Time_Timestamp_toWallTime___boxed(
    mut v_ts_220_: *mut leanh::LeanObject,
    mut v_offset_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Std_Time_Timestamp_toWallTime(v_ts_220_, v_offset_221_);
    leanh::lean_dec(v_offset_221_);
    leanh::lean_dec_ref(v_ts_220_);
    return v_res_222_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_ofWallTime___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_223_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_224_ = lean_int_neg(v___x_223_);
    return v___x_224_;
}
pub unsafe fn l_Std_Time_Timestamp_ofWallTime(
    mut v_wt_225_: *mut leanh::LeanObject,
    mut v_offset_226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_227_ = leanh::lean_ctor_get(v_wt_225_, 0);
    v_nano_228_ = leanh::lean_ctor_get(v_wt_225_, 1);
    v___x_229_ = lean_int_neg(v_offset_226_);
    v___x_230_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_ofWallTime___closed__0,
    );
    v___x_231_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_232_ = lean_int_mul(v_second_227_, v___x_231_);
    v___x_233_ = lean_int_add(v___x_232_, v_nano_228_);
    leanh::lean_dec(v___x_232_);
    v___x_234_ = lean_int_mul(v___x_229_, v___x_231_);
    leanh::lean_dec(v___x_229_);
    v___x_235_ = lean_int_add(v___x_234_, v___x_230_);
    leanh::lean_dec(v___x_234_);
    v___x_236_ = lean_int_add(v___x_233_, v___x_235_);
    leanh::lean_dec(v___x_235_);
    leanh::lean_dec(v___x_233_);
    v___x_237_ = l_Std_Time_Duration_ofNanoseconds(v___x_236_);
    leanh::lean_dec(v___x_236_);
    return v___x_237_;
}
pub unsafe fn l_Std_Time_Timestamp_ofWallTime___boxed(
    mut v_wt_238_: *mut leanh::LeanObject,
    mut v_offset_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_240_ = l_Std_Time_Timestamp_ofWallTime(v_wt_238_, v_offset_239_);
    leanh::lean_dec(v_offset_239_);
    leanh::lean_dec_ref(v_wt_238_);
    return v_res_240_;
}
pub unsafe fn l_Std_Time_WallTime_toTimestamp(
    mut v_wt_241_: *mut leanh::LeanObject,
    mut v_offset_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_243_ = leanh::lean_ctor_get(v_wt_241_, 0);
    v_nano_244_ = leanh::lean_ctor_get(v_wt_241_, 1);
    v___x_245_ = lean_int_neg(v_offset_242_);
    v___x_246_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_ofWallTime___closed__0,
    );
    v___x_247_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_248_ = lean_int_mul(v_second_243_, v___x_247_);
    v___x_249_ = lean_int_add(v___x_248_, v_nano_244_);
    leanh::lean_dec(v___x_248_);
    v___x_250_ = lean_int_mul(v___x_245_, v___x_247_);
    leanh::lean_dec(v___x_245_);
    v___x_251_ = lean_int_add(v___x_250_, v___x_246_);
    leanh::lean_dec(v___x_250_);
    v___x_252_ = lean_int_add(v___x_249_, v___x_251_);
    leanh::lean_dec(v___x_251_);
    leanh::lean_dec(v___x_249_);
    v___x_253_ = l_Std_Time_Duration_ofNanoseconds(v___x_252_);
    leanh::lean_dec(v___x_252_);
    return v___x_253_;
}
pub unsafe fn l_Std_Time_WallTime_toTimestamp___boxed(
    mut v_wt_254_: *mut leanh::LeanObject,
    mut v_offset_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Std_Time_WallTime_toTimestamp(v_wt_254_, v_offset_255_);
    leanh::lean_dec(v_offset_255_);
    leanh::lean_dec_ref(v_wt_254_);
    return v_res_256_;
}
pub unsafe fn l_Std_Time_WallTime_ofTimestamp(
    mut v_ts_257_: *mut leanh::LeanObject,
    mut v_offset_258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_259_ = leanh::lean_ctor_get(v_ts_257_, 0);
    v_nano_260_ = leanh::lean_ctor_get(v_ts_257_, 1);
    v___x_261_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_262_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_263_ = lean_int_mul(v_second_259_, v___x_262_);
    v___x_264_ = lean_int_add(v___x_263_, v_nano_260_);
    leanh::lean_dec(v___x_263_);
    v___x_265_ = lean_int_mul(v_offset_258_, v___x_262_);
    v___x_266_ = lean_int_add(v___x_265_, v___x_261_);
    leanh::lean_dec(v___x_265_);
    v___x_267_ = lean_int_add(v___x_264_, v___x_266_);
    leanh::lean_dec(v___x_266_);
    leanh::lean_dec(v___x_264_);
    v___x_268_ = l_Std_Time_Duration_ofNanoseconds(v___x_267_);
    leanh::lean_dec(v___x_267_);
    return v___x_268_;
}
pub unsafe fn l_Std_Time_WallTime_ofTimestamp___boxed(
    mut v_ts_269_: *mut leanh::LeanObject,
    mut v_offset_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Std_Time_WallTime_ofTimestamp(v_ts_269_, v_offset_270_);
    leanh::lean_dec(v_offset_270_);
    leanh::lean_dec_ref(v_ts_269_);
    return v_res_271_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_toWallTime___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = leanh::lean_unsigned_to_nat(86400);
    v___x_273_ = lean_nat_to_int(v___x_272_);
    return v___x_273_;
}
pub unsafe fn l_Std_Time_PlainDate_toWallTime(
    mut v_pd_274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_275_ = l_Std_Time_PlainDate_toEpochDay(v_pd_274_);
    v___x_276_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDate_toWallTime___closed__0,
    );
    v___x_277_ = lean_int_mul(v___x_275_, v___x_276_);
    leanh::lean_dec(v___x_275_);
    v___x_278_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_279_, 0, v___x_277_);
    leanh::lean_ctor_set(v___x_279_, 1, v___x_278_);
    return v___x_279_;
}
pub unsafe fn l_Std_Time_PlainDate_ofWallTime(
    mut v_wt_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_281_ = leanh::lean_ctor_get(v_wt_280_, 0);
    v___x_282_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDate_toWallTime___closed__0,
    );
    v___x_283_ = lean_int_div(v_second_281_, v___x_282_);
    v___x_284_ = l_Std_Time_PlainDate_ofEpochDay(v___x_283_);
    leanh::lean_dec(v___x_283_);
    return v___x_284_;
}
pub unsafe fn l_Std_Time_PlainDate_ofWallTime___boxed(
    mut v_wt_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Std_Time_PlainDate_ofWallTime(v_wt_285_);
    leanh::lean_dec_ref(v_wt_285_);
    return v_res_286_;
}
pub unsafe fn l_Std_Time_PlainDate_instHSubDuration___lam__0(
    mut v_x_287_: *mut leanh::LeanObject,
    mut v_y_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = l_Std_Time_PlainDate_toEpochDay(v_x_287_);
    v___x_290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDate_toWallTime___closed__0,
    );
    v___x_291_ = lean_int_mul(v___x_289_, v___x_290_);
    leanh::lean_dec(v___x_289_);
    v___x_292_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_293_ = l_Std_Time_PlainDate_toEpochDay(v_y_288_);
    v___x_294_ = lean_int_mul(v___x_293_, v___x_290_);
    leanh::lean_dec(v___x_293_);
    v___x_295_ = lean_int_neg(v___x_294_);
    leanh::lean_dec(v___x_294_);
    v___x_296_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_ofWallTime___closed__0,
    );
    v___x_297_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_298_ = lean_int_mul(v___x_291_, v___x_297_);
    leanh::lean_dec(v___x_291_);
    v___x_299_ = lean_int_add(v___x_298_, v___x_292_);
    leanh::lean_dec(v___x_298_);
    v___x_300_ = lean_int_mul(v___x_295_, v___x_297_);
    leanh::lean_dec(v___x_295_);
    v___x_301_ = lean_int_add(v___x_300_, v___x_296_);
    leanh::lean_dec(v___x_300_);
    v___x_302_ = lean_int_add(v___x_299_, v___x_301_);
    leanh::lean_dec(v___x_301_);
    leanh::lean_dec(v___x_299_);
    v___x_303_ = l_Std_Time_Duration_ofNanoseconds(v___x_302_);
    leanh::lean_dec(v___x_302_);
    return v___x_303_;
}
pub unsafe fn l_Std_Time_PlainTime_toWallTime(
    mut v_pt_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_306_);
    v___x_308_ = l_Std_Time_Duration_ofNanoseconds(v___x_307_);
    leanh::lean_dec(v___x_307_);
    return v___x_308_;
}
pub unsafe fn l_Std_Time_PlainTime_toWallTime___boxed(
    mut v_pt_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_310_ = l_Std_Time_PlainTime_toWallTime(v_pt_309_);
    leanh::lean_dec_ref(v_pt_309_);
    return v_res_310_;
}
pub unsafe fn l_Std_Time_PlainTime_ofWallTime(
    mut v_wt_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_312_ = leanh::lean_ctor_get(v_wt_311_, 0);
    v_nano_313_ = leanh::lean_ctor_get(v_wt_311_, 1);
    v___x_314_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_315_ = lean_int_mul(v_second_312_, v___x_314_);
    v_nanos_316_ = lean_int_add(v___x_315_, v_nano_313_);
    leanh::lean_dec(v___x_315_);
    v___x_317_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_316_);
    leanh::lean_dec(v_nanos_316_);
    return v___x_317_;
}
pub unsafe fn l_Std_Time_PlainTime_ofWallTime___boxed(
    mut v_wt_318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Std_Time_PlainTime_ofWallTime(v_wt_318_);
    leanh::lean_dec_ref(v_wt_318_);
    return v_res_319_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofPlainDate(
    mut v_date_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = l_Std_Time_PlainTime_midnight;
    v___x_322_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_322_, 0, v_date_320_);
    leanh::lean_ctor_set(v___x_322_, 1, v___x_321_);
    return v___x_322_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainDate(
    mut v_pdt_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_324_ = leanh::lean_ctor_get(v_pdt_323_, 0);
    leanh::lean_inc_ref(v_date_324_);
    return v_date_324_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainDate___boxed(
    mut v_pdt_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_325_);
    leanh::lean_dec_ref(v_pdt_325_);
    return v_res_326_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = leanh::lean_unsigned_to_nat(1);
    v___x_328_ = lean_nat_to_int(v___x_327_);
    return v___x_328_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = leanh::lean_unsigned_to_nat(11);
    v___x_330_ = lean_nat_to_int(v___x_329_);
    return v___x_330_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_331_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1,
    );
    v___x_332_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_333_ = lean_int_add(v___x_332_, v___x_331_);
    return v___x_333_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_335_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2,
    );
    v___x_336_ = lean_int_sub(v___x_335_, v___x_334_);
    return v___x_336_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_337_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_338_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3,
    );
    v_range_339_ = lean_int_add(v___x_338_, v___x_337_);
    return v_range_339_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_341_ = lean_int_sub(v___x_340_, v___x_340_);
    return v___x_341_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6()
-> *mut leanh::LeanObject {
    let mut v_range_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_342_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4,
    );
    v___x_343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5,
    );
    v___x_344_ = lean_int_emod(v___x_343_, v_range_342_);
    return v___x_344_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7()
-> *mut leanh::LeanObject {
    let mut v_range_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_345_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4,
    );
    v___x_346_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6,
    );
    v___x_347_ = lean_int_add(v___x_346_, v_range_345_);
    return v___x_347_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8()
-> *mut leanh::LeanObject {
    let mut v_range_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_348_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4,
    );
    v___x_349_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7,
    );
    v___x_350_ = lean_int_emod(v___x_349_, v_range_348_);
    return v___x_350_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_352_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8,
    );
    v___x_353_ = lean_int_add(v___x_352_, v___x_351_);
    return v___x_353_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = leanh::lean_unsigned_to_nat(30);
    v___x_355_ = lean_nat_to_int(v___x_354_);
    return v___x_355_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10,
    );
    v___x_357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_358_ = lean_int_add(v___x_357_, v___x_356_);
    return v___x_358_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_360_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11,
    );
    v___x_361_ = lean_int_sub(v___x_360_, v___x_359_);
    return v___x_361_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12,
    );
    v_range_364_ = lean_int_add(v___x_363_, v___x_362_);
    return v_range_364_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14()
-> *mut leanh::LeanObject {
    let mut v_range_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_365_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13,
    );
    v___x_366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5,
    );
    v___x_367_ = lean_int_emod(v___x_366_, v_range_365_);
    return v___x_367_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15()
-> *mut leanh::LeanObject {
    let mut v_range_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_368_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13,
    );
    v___x_369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14,
    );
    v___x_370_ = lean_int_add(v___x_369_, v_range_368_);
    return v___x_370_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16()
-> *mut leanh::LeanObject {
    let mut v_range_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_range_371_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13,
    );
    v___x_372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15,
    );
    v___x_373_ = lean_int_emod(v___x_372_, v_range_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16,
    );
    v___x_376_ = lean_int_add(v___x_375_, v___x_374_);
    return v___x_376_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17,
    );
    v___x_378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9,
    );
    v___x_379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_380_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_380_, 0, v___x_379_);
    leanh::lean_ctor_set(v___x_380_, 1, v___x_378_);
    leanh::lean_ctor_set(v___x_380_, 2, v___x_377_);
    return v___x_380_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofPlainTime(
    mut v_time_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18,
    );
    v___x_383_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_383_, 0, v___x_382_);
    leanh::lean_ctor_set(v___x_383_, 1, v_time_381_);
    return v___x_383_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainTime(
    mut v_pdt_384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_time_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_time_385_ = leanh::lean_ctor_get(v_pdt_384_, 1);
    leanh::lean_inc_ref(v_time_385_);
    return v_time_385_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainTime___boxed(
    mut v_pdt_386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_387_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_386_);
    leanh::lean_dec_ref(v_pdt_386_);
    return v_res_387_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instHSubDuration___lam__0(
    mut v_x_388_: *mut leanh::LeanObject,
    mut v_y_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Std_Time_PlainDateTime_toWallTime(v_y_389_);
    v_second_391_ = leanh::lean_ctor_get(v___x_390_, 0);
    leanh::lean_inc(v_second_391_);
    v_nano_392_ = leanh::lean_ctor_get(v___x_390_, 1);
    leanh::lean_inc(v_nano_392_);
    leanh::lean_dec_ref(v___x_390_);
    v___x_393_ = l_Std_Time_PlainDateTime_toWallTime(v_x_388_);
    v_second_394_ = leanh::lean_ctor_get(v___x_393_, 0);
    leanh::lean_inc(v_second_394_);
    v_nano_395_ = leanh::lean_ctor_get(v___x_393_, 1);
    leanh::lean_inc(v_nano_395_);
    leanh::lean_dec_ref(v___x_393_);
    v___x_396_ = lean_int_neg(v_second_391_);
    leanh::lean_dec(v_second_391_);
    v___x_397_ = lean_int_neg(v_nano_392_);
    leanh::lean_dec(v_nano_392_);
    v___x_398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_399_ = lean_int_mul(v_second_394_, v___x_398_);
    leanh::lean_dec(v_second_394_);
    v___x_400_ = lean_int_add(v___x_399_, v_nano_395_);
    leanh::lean_dec(v_nano_395_);
    leanh::lean_dec(v___x_399_);
    v___x_401_ = lean_int_mul(v___x_396_, v___x_398_);
    leanh::lean_dec(v___x_396_);
    v___x_402_ = lean_int_add(v___x_401_, v___x_397_);
    leanh::lean_dec(v___x_397_);
    leanh::lean_dec(v___x_401_);
    v___x_403_ = lean_int_add(v___x_400_, v___x_402_);
    leanh::lean_dec(v___x_402_);
    leanh::lean_dec(v___x_400_);
    v___x_404_ = l_Std_Time_Duration_ofNanoseconds(v___x_403_);
    leanh::lean_dec(v___x_403_);
    return v___x_404_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_DateTime(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_WallTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_Timestamp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_DateTime(builtin);
}