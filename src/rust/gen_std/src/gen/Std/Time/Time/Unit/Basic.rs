// Lean compiler output
// Module: Std.Time.Time.Unit.Basic
// Imports: Std.Time.Time.Unit.Hour Std.Time.Time.Unit.Millisecond
use crate::r#gen::Std::Time::Time::Unit::Hour::{
    initialize_Std_Time_Time_Unit_Hour, runtime_initialize_Std_Time_Time_Unit_Hour,
};
use crate::r#gen::Std::Time::Time::Unit::Millisecond::{
    initialize_Std_Time_Time_Unit_Millisecond, runtime_initialize_Std_Time_Time_Unit_Millisecond,
};
use crate::ffi::{lean_int_mul, lean_nat_to_int};
use crate::ffi::lean_int_div;
static mut l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_Offset_toSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_Offset_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_Offset_toHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_Offset_toSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_Offset_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Millisecond_Offset_toHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_Offset_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Second_Offset_toHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_219_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_220_ = lean_nat_to_int(v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMilliseconds(
    mut v_offset_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_223_ = lean_int_div(v_offset_221_, v___x_222_);
    return v___x_223_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMilliseconds___boxed(
    mut v_offset_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_225_ = l_Std_Time_Nanosecond_Offset_toMilliseconds(v_offset_224_);
    crate::leanh::lean_dec(v_offset_224_);
    return v_res_225_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMilliseconds(
    mut v_offset_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_227_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_228_ = lean_int_mul(v_offset_226_, v___x_227_);
    return v___x_228_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMilliseconds___boxed(
    mut v_offset_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Std_Time_Nanosecond_Offset_ofMilliseconds(v_offset_229_);
    crate::leanh::lean_dec(v_offset_229_);
    return v_res_230_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_232_ = lean_nat_to_int(v___x_231_);
    return v___x_232_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toSeconds(
    mut v_offset_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_235_ = lean_int_div(v_offset_233_, v___x_234_);
    return v___x_235_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toSeconds___boxed(
    mut v_offset_236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_237_ = l_Std_Time_Nanosecond_Offset_toSeconds(v_offset_236_);
    crate::leanh::lean_dec(v_offset_236_);
    return v_res_237_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofSeconds(
    mut v_offset_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_240_ = lean_int_mul(v_offset_238_, v___x_239_);
    return v___x_240_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofSeconds___boxed(
    mut v_offset_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Std_Time_Nanosecond_Offset_ofSeconds(v_offset_241_);
    crate::leanh::lean_dec(v_offset_241_);
    return v_res_242_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = crate::leanh::lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_244_ = lean_nat_to_int(v___x_243_);
    return v___x_244_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMinutes(
    mut v_offset_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_246_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_247_ = lean_int_div(v_offset_245_, v___x_246_);
    return v___x_247_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMinutes___boxed(
    mut v_offset_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Std_Time_Nanosecond_Offset_toMinutes(v_offset_248_);
    crate::leanh::lean_dec(v_offset_248_);
    return v_res_249_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMinutes(
    mut v_offset_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_252_ = lean_int_mul(v_offset_250_, v___x_251_);
    return v___x_252_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMinutes___boxed(
    mut v_offset_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Std_Time_Nanosecond_Offset_ofMinutes(v_offset_253_);
    crate::leanh::lean_dec(v_offset_253_);
    return v_res_254_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = crate::leanh::lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_256_ = lean_nat_to_int(v___x_255_);
    return v___x_256_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toHours(
    mut v_offset_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_259_ = lean_int_div(v_offset_257_, v___x_258_);
    return v___x_259_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toHours___boxed(
    mut v_offset_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Std_Time_Nanosecond_Offset_toHours(v_offset_260_);
    crate::leanh::lean_dec(v_offset_260_);
    return v_res_261_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofHours(
    mut v_offset_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_264_ = lean_int_mul(v_offset_262_, v___x_263_);
    return v___x_264_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofHours___boxed(
    mut v_offset_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Std_Time_Nanosecond_Offset_ofHours(v_offset_265_);
    crate::leanh::lean_dec(v_offset_265_);
    return v_res_266_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toNanoseconds(
    mut v_offset_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_269_ = lean_int_mul(v_offset_267_, v___x_268_);
    return v___x_269_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toNanoseconds___boxed(
    mut v_offset_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Std_Time_Millisecond_Offset_toNanoseconds(v_offset_270_);
    crate::leanh::lean_dec(v_offset_270_);
    return v_res_271_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofNanoseconds(
    mut v_offset_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_273_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_274_ = lean_int_div(v_offset_272_, v___x_273_);
    return v___x_274_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofNanoseconds___boxed(
    mut v_offset_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Std_Time_Millisecond_Offset_ofNanoseconds(v_offset_275_);
    crate::leanh::lean_dec(v_offset_275_);
    return v_res_276_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_278_ = lean_nat_to_int(v___x_277_);
    return v___x_278_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toSeconds(
    mut v_offset_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_281_ = lean_int_div(v_offset_279_, v___x_280_);
    return v___x_281_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toSeconds___boxed(
    mut v_offset_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Std_Time_Millisecond_Offset_toSeconds(v_offset_282_);
    crate::leanh::lean_dec(v_offset_282_);
    return v_res_283_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofSeconds(
    mut v_offset_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_286_ = lean_int_mul(v_offset_284_, v___x_285_);
    return v___x_286_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofSeconds___boxed(
    mut v_offset_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Std_Time_Millisecond_Offset_ofSeconds(v_offset_287_);
    crate::leanh::lean_dec(v_offset_287_);
    return v_res_288_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = crate::leanh::lean_unsigned_to_nat(60000);
    v___x_290_ = lean_nat_to_int(v___x_289_);
    return v___x_290_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toMinutes(
    mut v_offset_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_293_ = lean_int_div(v_offset_291_, v___x_292_);
    return v___x_293_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toMinutes___boxed(
    mut v_offset_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Std_Time_Millisecond_Offset_toMinutes(v_offset_294_);
    crate::leanh::lean_dec(v_offset_294_);
    return v_res_295_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofMinutes(
    mut v_offset_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_298_ = lean_int_mul(v_offset_296_, v___x_297_);
    return v___x_298_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofMinutes___boxed(
    mut v_offset_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Std_Time_Millisecond_Offset_ofMinutes(v_offset_299_);
    crate::leanh::lean_dec(v_offset_299_);
    return v_res_300_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toHours___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = crate::leanh::lean_unsigned_to_nat(3600000);
    v___x_302_ = lean_nat_to_int(v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toHours(
    mut v_offset_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_305_ = lean_int_div(v_offset_303_, v___x_304_);
    return v___x_305_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toHours___boxed(
    mut v_offset_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Std_Time_Millisecond_Offset_toHours(v_offset_306_);
    crate::leanh::lean_dec(v_offset_306_);
    return v_res_307_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofHours(
    mut v_offset_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_310_ = lean_int_mul(v_offset_308_, v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofHours___boxed(
    mut v_offset_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_Time_Millisecond_Offset_ofHours(v_offset_311_);
    crate::leanh::lean_dec(v_offset_311_);
    return v_res_312_;
}
pub unsafe fn l_Std_Time_Second_Offset_toNanoseconds(
    mut v_offset_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_314_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_315_ = lean_int_mul(v_offset_313_, v___x_314_);
    return v___x_315_;
}
pub unsafe fn l_Std_Time_Second_Offset_toNanoseconds___boxed(
    mut v_offset_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Time_Second_Offset_toNanoseconds(v_offset_316_);
    crate::leanh::lean_dec(v_offset_316_);
    return v_res_317_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofNanoseconds(
    mut v_offset_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_320_ = lean_int_div(v_offset_318_, v___x_319_);
    return v___x_320_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofNanoseconds___boxed(
    mut v_offset_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = l_Std_Time_Second_Offset_ofNanoseconds(v_offset_321_);
    crate::leanh::lean_dec(v_offset_321_);
    return v_res_322_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMilliseconds(
    mut v_offset_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_325_ = lean_int_mul(v_offset_323_, v___x_324_);
    return v___x_325_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMilliseconds___boxed(
    mut v_offset_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Std_Time_Second_Offset_toMilliseconds(v_offset_326_);
    crate::leanh::lean_dec(v_offset_326_);
    return v_res_327_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMilliseconds(
    mut v_offset_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_330_ = lean_int_div(v_offset_328_, v___x_329_);
    return v___x_330_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMilliseconds___boxed(
    mut v_offset_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Std_Time_Second_Offset_ofMilliseconds(v_offset_331_);
    crate::leanh::lean_dec(v_offset_331_);
    return v_res_332_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toMinutes___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_334_ = lean_nat_to_int(v___x_333_);
    return v___x_334_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMinutes(
    mut v_offset_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_337_ = lean_int_div(v_offset_335_, v___x_336_);
    return v___x_337_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMinutes___boxed(
    mut v_offset_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Time_Second_Offset_toMinutes(v_offset_338_);
    crate::leanh::lean_dec(v_offset_338_);
    return v_res_339_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMinutes(
    mut v_offset_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_342_ = lean_int_mul(v_offset_340_, v___x_341_);
    return v___x_342_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMinutes___boxed(
    mut v_offset_343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_344_ = l_Std_Time_Second_Offset_ofMinutes(v_offset_343_);
    crate::leanh::lean_dec(v_offset_343_);
    return v_res_344_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toHours___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_345_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_346_ = lean_nat_to_int(v___x_345_);
    return v___x_346_;
}
pub unsafe fn l_Std_Time_Second_Offset_toHours(
    mut v_offset_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_349_ = lean_int_div(v_offset_347_, v___x_348_);
    return v___x_349_;
}
pub unsafe fn l_Std_Time_Second_Offset_toHours___boxed(
    mut v_offset_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Std_Time_Second_Offset_toHours(v_offset_350_);
    crate::leanh::lean_dec(v_offset_350_);
    return v_res_351_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofHours(
    mut v_offset_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_353_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_354_ = lean_int_mul(v_offset_352_, v___x_353_);
    return v___x_354_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofHours___boxed(
    mut v_offset_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Std_Time_Second_Offset_ofHours(v_offset_355_);
    crate::leanh::lean_dec(v_offset_355_);
    return v_res_356_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toNanoseconds(
    mut v_offset_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_359_ = lean_int_mul(v_offset_357_, v___x_358_);
    return v___x_359_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toNanoseconds___boxed(
    mut v_offset_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Std_Time_Minute_Offset_toNanoseconds(v_offset_360_);
    crate::leanh::lean_dec(v_offset_360_);
    return v_res_361_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofNanoseconds(
    mut v_offset_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_364_ = lean_int_div(v_offset_362_, v___x_363_);
    return v___x_364_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofNanoseconds___boxed(
    mut v_offset_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Std_Time_Minute_Offset_ofNanoseconds(v_offset_365_);
    crate::leanh::lean_dec(v_offset_365_);
    return v_res_366_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toMilliseconds(
    mut v_offset_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_369_ = lean_int_mul(v_offset_367_, v___x_368_);
    return v___x_369_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toMilliseconds___boxed(
    mut v_offset_370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_371_ = l_Std_Time_Minute_Offset_toMilliseconds(v_offset_370_);
    crate::leanh::lean_dec(v_offset_370_);
    return v_res_371_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofMilliseconds(
    mut v_offset_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_374_ = lean_int_div(v_offset_372_, v___x_373_);
    return v___x_374_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofMilliseconds___boxed(
    mut v_offset_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l_Std_Time_Minute_Offset_ofMilliseconds(v_offset_375_);
    crate::leanh::lean_dec(v_offset_375_);
    return v_res_376_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toSeconds(
    mut v_offset_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_378_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_379_ = lean_int_mul(v_offset_377_, v___x_378_);
    return v___x_379_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toSeconds___boxed(
    mut v_offset_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_381_ = l_Std_Time_Minute_Offset_toSeconds(v_offset_380_);
    crate::leanh::lean_dec(v_offset_380_);
    return v_res_381_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofSeconds(
    mut v_offset_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_383_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_384_ = lean_int_div(v_offset_382_, v___x_383_);
    return v___x_384_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofSeconds___boxed(
    mut v_offset_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Std_Time_Minute_Offset_ofSeconds(v_offset_385_);
    crate::leanh::lean_dec(v_offset_385_);
    return v_res_386_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toHours(
    mut v_offset_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_389_ = lean_int_div(v_offset_387_, v___x_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toHours___boxed(
    mut v_offset_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_391_ = l_Std_Time_Minute_Offset_toHours(v_offset_390_);
    crate::leanh::lean_dec(v_offset_390_);
    return v_res_391_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofHours(
    mut v_offset_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_394_ = lean_int_mul(v_offset_392_, v___x_393_);
    return v___x_394_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofHours___boxed(
    mut v_offset_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Std_Time_Minute_Offset_ofHours(v_offset_395_);
    crate::leanh::lean_dec(v_offset_395_);
    return v_res_396_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toNanoseconds(
    mut v_offset_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_399_ = lean_int_mul(v_offset_397_, v___x_398_);
    return v___x_399_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toNanoseconds___boxed(
    mut v_offset_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_401_ = l_Std_Time_Hour_Offset_toNanoseconds(v_offset_400_);
    crate::leanh::lean_dec(v_offset_400_);
    return v_res_401_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofNanoseconds(
    mut v_offset_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_404_ = lean_int_div(v_offset_402_, v___x_403_);
    return v___x_404_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofNanoseconds___boxed(
    mut v_offset_405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_406_ = l_Std_Time_Hour_Offset_ofNanoseconds(v_offset_405_);
    crate::leanh::lean_dec(v_offset_405_);
    return v_res_406_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMilliseconds(
    mut v_offset_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_408_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_409_ = lean_int_mul(v_offset_407_, v___x_408_);
    return v___x_409_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMilliseconds___boxed(
    mut v_offset_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Std_Time_Hour_Offset_toMilliseconds(v_offset_410_);
    crate::leanh::lean_dec(v_offset_410_);
    return v_res_411_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMilliseconds(
    mut v_offset_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_414_ = lean_int_div(v_offset_412_, v___x_413_);
    return v___x_414_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMilliseconds___boxed(
    mut v_offset_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Time_Hour_Offset_ofMilliseconds(v_offset_415_);
    crate::leanh::lean_dec(v_offset_415_);
    return v_res_416_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toSeconds(
    mut v_offset_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_419_ = lean_int_mul(v_offset_417_, v___x_418_);
    return v___x_419_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toSeconds___boxed(
    mut v_offset_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Std_Time_Hour_Offset_toSeconds(v_offset_420_);
    crate::leanh::lean_dec(v_offset_420_);
    return v_res_421_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofSeconds(
    mut v_offset_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_424_ = lean_int_div(v_offset_422_, v___x_423_);
    return v___x_424_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofSeconds___boxed(
    mut v_offset_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_426_ = l_Std_Time_Hour_Offset_ofSeconds(v_offset_425_);
    crate::leanh::lean_dec(v_offset_425_);
    return v_res_426_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMinutes(
    mut v_offset_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_429_ = lean_int_mul(v_offset_427_, v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMinutes___boxed(
    mut v_offset_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Std_Time_Hour_Offset_toMinutes(v_offset_430_);
    crate::leanh::lean_dec(v_offset_430_);
    return v_res_431_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMinutes(
    mut v_offset_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_434_ = lean_int_div(v_offset_432_, v___x_433_);
    return v___x_434_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMinutes___boxed(
    mut v_offset_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Time_Hour_Offset_ofMinutes(v_offset_435_);
    crate::leanh::lean_dec(v_offset_435_);
    return v_res_436_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Hour(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Millisecond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Basic(
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
pub unsafe fn initialize_Std_Time_Time_Unit_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Hour(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Time_Unit_Millisecond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Basic(builtin);
}
