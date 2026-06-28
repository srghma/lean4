// Lean compiler output
// Module: Std.Time.DateTime
// Imports: Std.Time.Zoned.Offset Std.Time.DateTime.WallTime Std.Time.DateTime.Timestamp Std.Time.DateTime.PlainDateTime Std.Time.Date.Unit.Month
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_div, lean_int_emod};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Timestamp_toWallTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_toWallTime___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Timestamp_toWallTime___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_toWallTime___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Timestamp_ofWallTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_ofWallTime___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_toWallTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_toWallTime___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_PlainDate_instHSubDuration___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_instHSubDuration___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instHSubDuration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubDuration___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_PlainDate_instHSubDuration: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubDuration___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofPlainTime___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_instHSubDuration___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubDuration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubDuration: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_Time_Timestamp_toWallTime___closed__0() -> *mut LeanObject {
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v___x_204_ = lean_unsigned_to_nat(0);
    v___x_205_ = lean_nat_to_int(v___x_204_);
    return v___x_205_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_toWallTime___closed__1() -> *mut LeanObject {
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    v___x_206_ = lean_unsigned_to_nat(1000000000);
    v___x_207_ = lean_nat_to_int(v___x_206_);
    return v___x_207_;
}
pub unsafe fn l_Std_Time_Timestamp_toWallTime(
    mut v_ts_208_: *mut LeanObject,
    mut v_offset_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    v_second_210_ = lean_ctor_get(v_ts_208_, 0);
    v_nano_211_ = lean_ctor_get(v_ts_208_, 1);
    v___x_212_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_213_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_214_ = lean_int_mul(v_second_210_, v___x_213_);
    v___x_215_ = lean_int_add(v___x_214_, v_nano_211_);
    lean_dec(v___x_214_);
    v___x_216_ = lean_int_mul(v_offset_209_, v___x_213_);
    v___x_217_ = lean_int_add(v___x_216_, v___x_212_);
    lean_dec(v___x_216_);
    v___x_218_ = lean_int_add(v___x_215_, v___x_217_);
    lean_dec(v___x_217_);
    lean_dec(v___x_215_);
    v___x_219_ = l_Std_Time_Duration_ofNanoseconds(v___x_218_);
    lean_dec(v___x_218_);
    return v___x_219_;
}
pub unsafe fn l_Std_Time_Timestamp_toWallTime___boxed(
    mut v_ts_220_: *mut LeanObject,
    mut v_offset_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Std_Time_Timestamp_toWallTime(v_ts_220_, v_offset_221_);
    lean_dec(v_offset_221_);
    lean_dec_ref(v_ts_220_);
    return v_res_222_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_ofWallTime___closed__0() -> *mut LeanObject {
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    v___x_223_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_224_ = lean_int_neg(v___x_223_);
    return v___x_224_;
}
pub unsafe fn l_Std_Time_Timestamp_ofWallTime(
    mut v_wt_225_: *mut LeanObject,
    mut v_offset_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    v_second_227_ = lean_ctor_get(v_wt_225_, 0);
    v_nano_228_ = lean_ctor_get(v_wt_225_, 1);
    v___x_229_ = lean_int_neg(v_offset_226_);
    v___x_230_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_ofWallTime___closed__0,
    );
    v___x_231_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_232_ = lean_int_mul(v_second_227_, v___x_231_);
    v___x_233_ = lean_int_add(v___x_232_, v_nano_228_);
    lean_dec(v___x_232_);
    v___x_234_ = lean_int_mul(v___x_229_, v___x_231_);
    lean_dec(v___x_229_);
    v___x_235_ = lean_int_add(v___x_234_, v___x_230_);
    lean_dec(v___x_234_);
    v___x_236_ = lean_int_add(v___x_233_, v___x_235_);
    lean_dec(v___x_235_);
    lean_dec(v___x_233_);
    v___x_237_ = l_Std_Time_Duration_ofNanoseconds(v___x_236_);
    lean_dec(v___x_236_);
    return v___x_237_;
}
pub unsafe fn l_Std_Time_Timestamp_ofWallTime___boxed(
    mut v_wt_238_: *mut LeanObject,
    mut v_offset_239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_240_: *mut LeanObject = core::ptr::null_mut();
    v_res_240_ = l_Std_Time_Timestamp_ofWallTime(v_wt_238_, v_offset_239_);
    lean_dec(v_offset_239_);
    lean_dec_ref(v_wt_238_);
    return v_res_240_;
}
pub unsafe fn l_Std_Time_WallTime_toTimestamp(
    mut v_wt_241_: *mut LeanObject,
    mut v_offset_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    v_second_243_ = lean_ctor_get(v_wt_241_, 0);
    v_nano_244_ = lean_ctor_get(v_wt_241_, 1);
    v___x_245_ = lean_int_neg(v_offset_242_);
    v___x_246_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_ofWallTime___closed__0,
    );
    v___x_247_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_248_ = lean_int_mul(v_second_243_, v___x_247_);
    v___x_249_ = lean_int_add(v___x_248_, v_nano_244_);
    lean_dec(v___x_248_);
    v___x_250_ = lean_int_mul(v___x_245_, v___x_247_);
    lean_dec(v___x_245_);
    v___x_251_ = lean_int_add(v___x_250_, v___x_246_);
    lean_dec(v___x_250_);
    v___x_252_ = lean_int_add(v___x_249_, v___x_251_);
    lean_dec(v___x_251_);
    lean_dec(v___x_249_);
    v___x_253_ = l_Std_Time_Duration_ofNanoseconds(v___x_252_);
    lean_dec(v___x_252_);
    return v___x_253_;
}
pub unsafe fn l_Std_Time_WallTime_toTimestamp___boxed(
    mut v_wt_254_: *mut LeanObject,
    mut v_offset_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_256_: *mut LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Std_Time_WallTime_toTimestamp(v_wt_254_, v_offset_255_);
    lean_dec(v_offset_255_);
    lean_dec_ref(v_wt_254_);
    return v_res_256_;
}
pub unsafe fn l_Std_Time_WallTime_ofTimestamp(
    mut v_ts_257_: *mut LeanObject,
    mut v_offset_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    v_second_259_ = lean_ctor_get(v_ts_257_, 0);
    v_nano_260_ = lean_ctor_get(v_ts_257_, 1);
    v___x_261_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_263_ = lean_int_mul(v_second_259_, v___x_262_);
    v___x_264_ = lean_int_add(v___x_263_, v_nano_260_);
    lean_dec(v___x_263_);
    v___x_265_ = lean_int_mul(v_offset_258_, v___x_262_);
    v___x_266_ = lean_int_add(v___x_265_, v___x_261_);
    lean_dec(v___x_265_);
    v___x_267_ = lean_int_add(v___x_264_, v___x_266_);
    lean_dec(v___x_266_);
    lean_dec(v___x_264_);
    v___x_268_ = l_Std_Time_Duration_ofNanoseconds(v___x_267_);
    lean_dec(v___x_267_);
    return v___x_268_;
}
pub unsafe fn l_Std_Time_WallTime_ofTimestamp___boxed(
    mut v_ts_269_: *mut LeanObject,
    mut v_offset_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_271_: *mut LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Std_Time_WallTime_ofTimestamp(v_ts_269_, v_offset_270_);
    lean_dec(v_offset_270_);
    lean_dec_ref(v_ts_269_);
    return v_res_271_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_toWallTime___closed__0() -> *mut LeanObject {
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    v___x_272_ = lean_unsigned_to_nat(86400);
    v___x_273_ = lean_nat_to_int(v___x_272_);
    return v___x_273_;
}
pub unsafe fn l_Std_Time_PlainDate_toWallTime(mut v_pd_274_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    v___x_275_ = l_Std_Time_PlainDate_toEpochDay(v_pd_274_);
    v___x_276_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDate_toWallTime___closed__0,
    );
    v___x_277_ = lean_int_mul(v___x_275_, v___x_276_);
    lean_dec(v___x_275_);
    v___x_278_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_279_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_279_, 0, v___x_277_);
    lean_ctor_set(v___x_279_, 1, v___x_278_);
    return v___x_279_;
}
pub unsafe fn l_Std_Time_PlainDate_ofWallTime(mut v_wt_280_: *mut LeanObject) -> *mut LeanObject {
    let mut v_second_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    v_second_281_ = lean_ctor_get(v_wt_280_, 0);
    v___x_282_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDate_toWallTime___closed__0,
    );
    v___x_283_ = lean_int_div(v_second_281_, v___x_282_);
    v___x_284_ = l_Std_Time_PlainDate_ofEpochDay(v___x_283_);
    lean_dec(v___x_283_);
    return v___x_284_;
}
pub unsafe fn l_Std_Time_PlainDate_ofWallTime___boxed(
    mut v_wt_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_286_: *mut LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Std_Time_PlainDate_ofWallTime(v_wt_285_);
    lean_dec_ref(v_wt_285_);
    return v_res_286_;
}
pub unsafe fn l_Std_Time_PlainDate_instHSubDuration___lam__0(
    mut v_x_287_: *mut LeanObject,
    mut v_y_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v___x_289_ = l_Std_Time_PlainDate_toEpochDay(v_x_287_);
    v___x_290_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDate_toWallTime___closed__0,
    );
    v___x_291_ = lean_int_mul(v___x_289_, v___x_290_);
    lean_dec(v___x_289_);
    v___x_292_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__0,
    );
    v___x_293_ = l_Std_Time_PlainDate_toEpochDay(v_y_288_);
    v___x_294_ = lean_int_mul(v___x_293_, v___x_290_);
    lean_dec(v___x_293_);
    v___x_295_ = lean_int_neg(v___x_294_);
    lean_dec(v___x_294_);
    v___x_296_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofWallTime___closed__0_once),
        _init_l_Std_Time_Timestamp_ofWallTime___closed__0,
    );
    v___x_297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_298_ = lean_int_mul(v___x_291_, v___x_297_);
    lean_dec(v___x_291_);
    v___x_299_ = lean_int_add(v___x_298_, v___x_292_);
    lean_dec(v___x_298_);
    v___x_300_ = lean_int_mul(v___x_295_, v___x_297_);
    lean_dec(v___x_295_);
    v___x_301_ = lean_int_add(v___x_300_, v___x_296_);
    lean_dec(v___x_300_);
    v___x_302_ = lean_int_add(v___x_299_, v___x_301_);
    lean_dec(v___x_301_);
    lean_dec(v___x_299_);
    v___x_303_ = l_Std_Time_Duration_ofNanoseconds(v___x_302_);
    lean_dec(v___x_302_);
    return v___x_303_;
}
pub unsafe fn l_Std_Time_PlainTime_toWallTime(mut v_pt_306_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_306_);
    v___x_308_ = l_Std_Time_Duration_ofNanoseconds(v___x_307_);
    lean_dec(v___x_307_);
    return v___x_308_;
}
pub unsafe fn l_Std_Time_PlainTime_toWallTime___boxed(
    mut v_pt_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_310_: *mut LeanObject = core::ptr::null_mut();
    v_res_310_ = l_Std_Time_PlainTime_toWallTime(v_pt_309_);
    lean_dec_ref(v_pt_309_);
    return v_res_310_;
}
pub unsafe fn l_Std_Time_PlainTime_ofWallTime(mut v_wt_311_: *mut LeanObject) -> *mut LeanObject {
    let mut v_second_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    v_second_312_ = lean_ctor_get(v_wt_311_, 0);
    v_nano_313_ = lean_ctor_get(v_wt_311_, 1);
    v___x_314_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_315_ = lean_int_mul(v_second_312_, v___x_314_);
    v_nanos_316_ = lean_int_add(v___x_315_, v_nano_313_);
    lean_dec(v___x_315_);
    v___x_317_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_316_);
    lean_dec(v_nanos_316_);
    return v___x_317_;
}
pub unsafe fn l_Std_Time_PlainTime_ofWallTime___boxed(
    mut v_wt_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_319_: *mut LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Std_Time_PlainTime_ofWallTime(v_wt_318_);
    lean_dec_ref(v_wt_318_);
    return v_res_319_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofPlainDate(
    mut v_date_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    v___x_321_ = l_Std_Time_PlainTime_midnight;
    v___x_322_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_322_, 0, v_date_320_);
    lean_ctor_set(v___x_322_, 1, v___x_321_);
    return v___x_322_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainDate(
    mut v_pdt_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_324_: *mut LeanObject = core::ptr::null_mut();
    v_date_324_ = lean_ctor_get(v_pdt_323_, 0);
    lean_inc_ref(v_date_324_);
    return v_date_324_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainDate___boxed(
    mut v_pdt_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Std_Time_PlainDateTime_toPlainDate(v_pdt_325_);
    lean_dec_ref(v_pdt_325_);
    return v_res_326_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0() -> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_unsigned_to_nat(1);
    v___x_328_ = lean_nat_to_int(v___x_327_);
    return v___x_328_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1() -> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v___x_329_ = lean_unsigned_to_nat(11);
    v___x_330_ = lean_nat_to_int(v___x_329_);
    return v___x_330_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2() -> *mut LeanObject {
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v___x_331_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1,
    );
    v___x_332_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_333_ = lean_int_add(v___x_332_, v___x_331_);
    return v___x_333_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3() -> *mut LeanObject {
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_335_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2,
    );
    v___x_336_ = lean_int_sub(v___x_335_, v___x_334_);
    return v___x_336_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4() -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_338_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3,
    );
    v_range_339_ = lean_int_add(v___x_338_, v___x_337_);
    return v_range_339_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5() -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_341_ = lean_int_sub(v___x_340_, v___x_340_);
    return v___x_341_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6() -> *mut LeanObject {
    let mut v_range_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v_range_342_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4,
    );
    v___x_343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5,
    );
    v___x_344_ = lean_int_emod(v___x_343_, v_range_342_);
    return v___x_344_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7() -> *mut LeanObject {
    let mut v_range_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    v_range_345_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4,
    );
    v___x_346_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6,
    );
    v___x_347_ = lean_int_add(v___x_346_, v_range_345_);
    return v___x_347_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8() -> *mut LeanObject {
    let mut v_range_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v_range_348_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4,
    );
    v___x_349_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7,
    );
    v___x_350_ = lean_int_emod(v___x_349_, v_range_348_);
    return v___x_350_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9() -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_352_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8,
    );
    v___x_353_ = lean_int_add(v___x_352_, v___x_351_);
    return v___x_353_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10() -> *mut LeanObject {
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_354_ = lean_unsigned_to_nat(30);
    v___x_355_ = lean_nat_to_int(v___x_354_);
    return v___x_355_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10,
    );
    v___x_357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_358_ = lean_int_add(v___x_357_, v___x_356_);
    return v___x_358_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12() -> *mut LeanObject {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    v___x_359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_360_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11,
    );
    v___x_361_ = lean_int_sub(v___x_360_, v___x_359_);
    return v___x_361_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13() -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12,
    );
    v_range_364_ = lean_int_add(v___x_363_, v___x_362_);
    return v_range_364_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14() -> *mut LeanObject {
    let mut v_range_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    v_range_365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13,
    );
    v___x_366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5,
    );
    v___x_367_ = lean_int_emod(v___x_366_, v_range_365_);
    return v___x_367_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15() -> *mut LeanObject {
    let mut v_range_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v_range_368_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13,
    );
    v___x_369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14,
    );
    v___x_370_ = lean_int_add(v___x_369_, v_range_368_);
    return v___x_370_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16() -> *mut LeanObject {
    let mut v_range_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v_range_371_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13,
    );
    v___x_372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15,
    );
    v___x_373_ = lean_int_emod(v___x_372_, v_range_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17() -> *mut LeanObject {
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    v___x_374_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_375_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16,
    );
    v___x_376_ = lean_int_add(v___x_375_, v___x_374_);
    return v___x_376_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18() -> *mut LeanObject {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17,
    );
    v___x_378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9,
    );
    v___x_379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0,
    );
    v___x_380_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_380_, 0, v___x_379_);
    lean_ctor_set(v___x_380_, 1, v___x_378_);
    lean_ctor_set(v___x_380_, 2, v___x_377_);
    return v___x_380_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofPlainTime(
    mut v_time_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_382_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once),
        _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18,
    );
    v___x_383_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_383_, 0, v___x_382_);
    lean_ctor_set(v___x_383_, 1, v_time_381_);
    return v___x_383_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainTime(
    mut v_pdt_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_385_: *mut LeanObject = core::ptr::null_mut();
    v_time_385_ = lean_ctor_get(v_pdt_384_, 1);
    lean_inc_ref(v_time_385_);
    return v_time_385_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toPlainTime___boxed(
    mut v_pdt_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l_Std_Time_PlainDateTime_toPlainTime(v_pdt_386_);
    lean_dec_ref(v_pdt_386_);
    return v_res_387_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instHSubDuration___lam__0(
    mut v_x_388_: *mut LeanObject,
    mut v_y_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Std_Time_PlainDateTime_toWallTime(v_y_389_);
    v_second_391_ = lean_ctor_get(v___x_390_, 0);
    lean_inc(v_second_391_);
    v_nano_392_ = lean_ctor_get(v___x_390_, 1);
    lean_inc(v_nano_392_);
    lean_dec_ref(v___x_390_);
    v___x_393_ = l_Std_Time_PlainDateTime_toWallTime(v_x_388_);
    v_second_394_ = lean_ctor_get(v___x_393_, 0);
    lean_inc(v_second_394_);
    v_nano_395_ = lean_ctor_get(v___x_393_, 1);
    lean_inc(v_nano_395_);
    lean_dec_ref(v___x_393_);
    v___x_396_ = lean_int_neg(v_second_391_);
    lean_dec(v_second_391_);
    v___x_397_ = lean_int_neg(v_nano_392_);
    lean_dec(v_nano_392_);
    v___x_398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toWallTime___closed__1_once),
        _init_l_Std_Time_Timestamp_toWallTime___closed__1,
    );
    v___x_399_ = lean_int_mul(v_second_394_, v___x_398_);
    lean_dec(v_second_394_);
    v___x_400_ = lean_int_add(v___x_399_, v_nano_395_);
    lean_dec(v_nano_395_);
    lean_dec(v___x_399_);
    v___x_401_ = lean_int_mul(v___x_396_, v___x_398_);
    lean_dec(v___x_396_);
    v___x_402_ = lean_int_add(v___x_401_, v___x_397_);
    lean_dec(v___x_397_);
    lean_dec(v___x_401_);
    v___x_403_ = lean_int_add(v___x_400_, v___x_402_);
    lean_dec(v___x_402_);
    lean_dec(v___x_400_);
    v___x_404_ = l_Std_Time_Duration_ofNanoseconds(v___x_403_);
    lean_dec(v___x_403_);
    return v___x_404_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_Offset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_WallTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_Timestamp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_DateTime(builtin);
}
