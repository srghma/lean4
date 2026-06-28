// Lean compiler output
// Module: Std.Time.Time.Unit.Basic
// Imports: Std.Time.Time.Unit.Hour Std.Time.Time.Unit.Millisecond
use crate::r#gen::Std::Time::Time::Unit::Hour::{
    initialize_Std_Time_Time_Unit_Hour, runtime_initialize_Std_Time_Time_Unit_Hour,
};
use crate::r#gen::Std::Time::Time::Unit::Millisecond::{
    initialize_Std_Time_Time_Unit_Millisecond, runtime_initialize_Std_Time_Time_Unit_Millisecond,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_mul, lean_nat_to_int};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_div;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_cstr_to_nat, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Nanosecond_Offset_toSeconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Nanosecond_Offset_toMinutes___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Nanosecond_Offset_toHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Nanosecond_Offset_toHours___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_Offset_toSeconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_Offset_toMinutes___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Millisecond_Offset_toHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Millisecond_Offset_toHours___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Second_Offset_toMinutes___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Second_Offset_toHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Second_Offset_toHours___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_219_ = lean_unsigned_to_nat(1000000);
    v___x_220_ = lean_nat_to_int(v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMilliseconds(
    mut v_offset_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    v___x_222_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_223_ = lean_int_div(v_offset_221_, v___x_222_);
    return v___x_223_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMilliseconds___boxed(
    mut v_offset_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_225_: *mut LeanObject = core::ptr::null_mut();
    v_res_225_ = l_Std_Time_Nanosecond_Offset_toMilliseconds(v_offset_224_);
    lean_dec(v_offset_224_);
    return v_res_225_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMilliseconds(
    mut v_offset_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_227_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_228_ = lean_int_mul(v_offset_226_, v___x_227_);
    return v___x_228_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMilliseconds___boxed(
    mut v_offset_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_230_: *mut LeanObject = core::ptr::null_mut();
    v_res_230_ = l_Std_Time_Nanosecond_Offset_ofMilliseconds(v_offset_229_);
    lean_dec(v_offset_229_);
    return v_res_230_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0() -> *mut LeanObject {
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v___x_231_ = lean_unsigned_to_nat(1000000000);
    v___x_232_ = lean_nat_to_int(v___x_231_);
    return v___x_232_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toSeconds(
    mut v_offset_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    v___x_234_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_235_ = lean_int_div(v_offset_233_, v___x_234_);
    return v___x_235_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toSeconds___boxed(
    mut v_offset_236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_237_: *mut LeanObject = core::ptr::null_mut();
    v_res_237_ = l_Std_Time_Nanosecond_Offset_toSeconds(v_offset_236_);
    lean_dec(v_offset_236_);
    return v_res_237_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofSeconds(
    mut v_offset_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    v___x_239_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_240_ = lean_int_mul(v_offset_238_, v___x_239_);
    return v___x_240_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofSeconds___boxed(
    mut v_offset_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Std_Time_Nanosecond_Offset_ofSeconds(v_offset_241_);
    lean_dec(v_offset_241_);
    return v_res_242_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    v___x_243_ = lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_244_ = lean_nat_to_int(v___x_243_);
    return v___x_244_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMinutes(
    mut v_offset_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    v___x_246_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_247_ = lean_int_div(v_offset_245_, v___x_246_);
    return v___x_247_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toMinutes___boxed(
    mut v_offset_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_249_: *mut LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Std_Time_Nanosecond_Offset_toMinutes(v_offset_248_);
    lean_dec(v_offset_248_);
    return v_res_249_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMinutes(
    mut v_offset_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v___x_251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_252_ = lean_int_mul(v_offset_250_, v___x_251_);
    return v___x_252_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofMinutes___boxed(
    mut v_offset_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Std_Time_Nanosecond_Offset_ofMinutes(v_offset_253_);
    lean_dec(v_offset_253_);
    return v_res_254_;
}
pub unsafe fn _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0() -> *mut LeanObject {
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v___x_255_ = lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_256_ = lean_nat_to_int(v___x_255_);
    return v___x_256_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toHours(
    mut v_offset_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    v___x_258_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_259_ = lean_int_div(v_offset_257_, v___x_258_);
    return v___x_259_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_toHours___boxed(
    mut v_offset_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Std_Time_Nanosecond_Offset_toHours(v_offset_260_);
    lean_dec(v_offset_260_);
    return v_res_261_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofHours(
    mut v_offset_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    v___x_263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_264_ = lean_int_mul(v_offset_262_, v___x_263_);
    return v___x_264_;
}
pub unsafe fn l_Std_Time_Nanosecond_Offset_ofHours___boxed(
    mut v_offset_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_266_: *mut LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Std_Time_Nanosecond_Offset_ofHours(v_offset_265_);
    lean_dec(v_offset_265_);
    return v_res_266_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toNanoseconds(
    mut v_offset_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_269_ = lean_int_mul(v_offset_267_, v___x_268_);
    return v___x_269_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toNanoseconds___boxed(
    mut v_offset_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_271_: *mut LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Std_Time_Millisecond_Offset_toNanoseconds(v_offset_270_);
    lean_dec(v_offset_270_);
    return v_res_271_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofNanoseconds(
    mut v_offset_272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    v___x_273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMilliseconds___closed__0,
    );
    v___x_274_ = lean_int_div(v_offset_272_, v___x_273_);
    return v___x_274_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofNanoseconds___boxed(
    mut v_offset_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_276_: *mut LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Std_Time_Millisecond_Offset_ofNanoseconds(v_offset_275_);
    lean_dec(v_offset_275_);
    return v_res_276_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0() -> *mut LeanObject {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    v___x_277_ = lean_unsigned_to_nat(1000);
    v___x_278_ = lean_nat_to_int(v___x_277_);
    return v___x_278_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toSeconds(
    mut v_offset_279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    v___x_280_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_281_ = lean_int_div(v_offset_279_, v___x_280_);
    return v___x_281_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toSeconds___boxed(
    mut v_offset_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_283_: *mut LeanObject = core::ptr::null_mut();
    v_res_283_ = l_Std_Time_Millisecond_Offset_toSeconds(v_offset_282_);
    lean_dec(v_offset_282_);
    return v_res_283_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofSeconds(
    mut v_offset_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v___x_285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_286_ = lean_int_mul(v_offset_284_, v___x_285_);
    return v___x_286_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofSeconds___boxed(
    mut v_offset_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_288_: *mut LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Std_Time_Millisecond_Offset_ofSeconds(v_offset_287_);
    lean_dec(v_offset_287_);
    return v_res_288_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_289_ = lean_unsigned_to_nat(60000);
    v___x_290_ = lean_nat_to_int(v___x_289_);
    return v___x_290_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toMinutes(
    mut v_offset_291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    v___x_292_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_293_ = lean_int_div(v_offset_291_, v___x_292_);
    return v___x_293_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toMinutes___boxed(
    mut v_offset_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Std_Time_Millisecond_Offset_toMinutes(v_offset_294_);
    lean_dec(v_offset_294_);
    return v_res_295_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofMinutes(
    mut v_offset_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_298_ = lean_int_mul(v_offset_296_, v___x_297_);
    return v___x_298_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofMinutes___boxed(
    mut v_offset_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_300_: *mut LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Std_Time_Millisecond_Offset_ofMinutes(v_offset_299_);
    lean_dec(v_offset_299_);
    return v_res_300_;
}
pub unsafe fn _init_l_Std_Time_Millisecond_Offset_toHours___closed__0() -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = lean_unsigned_to_nat(3600000);
    v___x_302_ = lean_nat_to_int(v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toHours(
    mut v_offset_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    v___x_304_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_305_ = lean_int_div(v_offset_303_, v___x_304_);
    return v___x_305_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_toHours___boxed(
    mut v_offset_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_307_: *mut LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Std_Time_Millisecond_Offset_toHours(v_offset_306_);
    lean_dec(v_offset_306_);
    return v_res_307_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofHours(
    mut v_offset_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_309_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_310_ = lean_int_mul(v_offset_308_, v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Std_Time_Millisecond_Offset_ofHours___boxed(
    mut v_offset_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_312_: *mut LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_Time_Millisecond_Offset_ofHours(v_offset_311_);
    lean_dec(v_offset_311_);
    return v_res_312_;
}
pub unsafe fn l_Std_Time_Second_Offset_toNanoseconds(
    mut v_offset_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v___x_314_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_315_ = lean_int_mul(v_offset_313_, v___x_314_);
    return v___x_315_;
}
pub unsafe fn l_Std_Time_Second_Offset_toNanoseconds___boxed(
    mut v_offset_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_317_: *mut LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Time_Second_Offset_toNanoseconds(v_offset_316_);
    lean_dec(v_offset_316_);
    return v_res_317_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofNanoseconds(
    mut v_offset_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    v___x_319_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toSeconds___closed__0,
    );
    v___x_320_ = lean_int_div(v_offset_318_, v___x_319_);
    return v___x_320_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofNanoseconds___boxed(
    mut v_offset_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_322_: *mut LeanObject = core::ptr::null_mut();
    v_res_322_ = l_Std_Time_Second_Offset_ofNanoseconds(v_offset_321_);
    lean_dec(v_offset_321_);
    return v_res_322_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMilliseconds(
    mut v_offset_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_325_ = lean_int_mul(v_offset_323_, v___x_324_);
    return v___x_325_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMilliseconds___boxed(
    mut v_offset_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Std_Time_Second_Offset_toMilliseconds(v_offset_326_);
    lean_dec(v_offset_326_);
    return v_res_327_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMilliseconds(
    mut v_offset_328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v___x_329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toSeconds___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toSeconds___closed__0,
    );
    v___x_330_ = lean_int_div(v_offset_328_, v___x_329_);
    return v___x_330_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMilliseconds___boxed(
    mut v_offset_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_332_: *mut LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Std_Time_Second_Offset_ofMilliseconds(v_offset_331_);
    lean_dec(v_offset_331_);
    return v_res_332_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    v___x_333_ = lean_unsigned_to_nat(60);
    v___x_334_ = lean_nat_to_int(v___x_333_);
    return v___x_334_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMinutes(
    mut v_offset_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    v___x_336_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_337_ = lean_int_div(v_offset_335_, v___x_336_);
    return v___x_337_;
}
pub unsafe fn l_Std_Time_Second_Offset_toMinutes___boxed(
    mut v_offset_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Time_Second_Offset_toMinutes(v_offset_338_);
    lean_dec(v_offset_338_);
    return v_res_339_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMinutes(
    mut v_offset_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_341_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_342_ = lean_int_mul(v_offset_340_, v___x_341_);
    return v___x_342_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofMinutes___boxed(
    mut v_offset_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_344_: *mut LeanObject = core::ptr::null_mut();
    v_res_344_ = l_Std_Time_Second_Offset_ofMinutes(v_offset_343_);
    lean_dec(v_offset_343_);
    return v_res_344_;
}
pub unsafe fn _init_l_Std_Time_Second_Offset_toHours___closed__0() -> *mut LeanObject {
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    v___x_345_ = lean_unsigned_to_nat(3600);
    v___x_346_ = lean_nat_to_int(v___x_345_);
    return v___x_346_;
}
pub unsafe fn l_Std_Time_Second_Offset_toHours(
    mut v_offset_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_349_ = lean_int_div(v_offset_347_, v___x_348_);
    return v___x_349_;
}
pub unsafe fn l_Std_Time_Second_Offset_toHours___boxed(
    mut v_offset_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Std_Time_Second_Offset_toHours(v_offset_350_);
    lean_dec(v_offset_350_);
    return v_res_351_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofHours(
    mut v_offset_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_353_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_354_ = lean_int_mul(v_offset_352_, v___x_353_);
    return v___x_354_;
}
pub unsafe fn l_Std_Time_Second_Offset_ofHours___boxed(
    mut v_offset_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_356_: *mut LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Std_Time_Second_Offset_ofHours(v_offset_355_);
    lean_dec(v_offset_355_);
    return v_res_356_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toNanoseconds(
    mut v_offset_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_359_ = lean_int_mul(v_offset_357_, v___x_358_);
    return v___x_359_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toNanoseconds___boxed(
    mut v_offset_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_361_: *mut LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Std_Time_Minute_Offset_toNanoseconds(v_offset_360_);
    lean_dec(v_offset_360_);
    return v_res_361_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofNanoseconds(
    mut v_offset_362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toMinutes___closed__0,
    );
    v___x_364_ = lean_int_div(v_offset_362_, v___x_363_);
    return v___x_364_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofNanoseconds___boxed(
    mut v_offset_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_366_: *mut LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Std_Time_Minute_Offset_ofNanoseconds(v_offset_365_);
    lean_dec(v_offset_365_);
    return v_res_366_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toMilliseconds(
    mut v_offset_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_369_ = lean_int_mul(v_offset_367_, v___x_368_);
    return v___x_369_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toMilliseconds___boxed(
    mut v_offset_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_371_: *mut LeanObject = core::ptr::null_mut();
    v_res_371_ = l_Std_Time_Minute_Offset_toMilliseconds(v_offset_370_);
    lean_dec(v_offset_370_);
    return v_res_371_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofMilliseconds(
    mut v_offset_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toMinutes___closed__0,
    );
    v___x_374_ = lean_int_div(v_offset_372_, v___x_373_);
    return v___x_374_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofMilliseconds___boxed(
    mut v_offset_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_376_: *mut LeanObject = core::ptr::null_mut();
    v_res_376_ = l_Std_Time_Minute_Offset_ofMilliseconds(v_offset_375_);
    lean_dec(v_offset_375_);
    return v_res_376_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toSeconds(
    mut v_offset_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_379_ = lean_int_mul(v_offset_377_, v___x_378_);
    return v___x_379_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toSeconds___boxed(
    mut v_offset_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_381_: *mut LeanObject = core::ptr::null_mut();
    v_res_381_ = l_Std_Time_Minute_Offset_toSeconds(v_offset_380_);
    lean_dec(v_offset_380_);
    return v_res_381_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofSeconds(
    mut v_offset_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_383_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_384_ = lean_int_div(v_offset_382_, v___x_383_);
    return v___x_384_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofSeconds___boxed(
    mut v_offset_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_386_: *mut LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Std_Time_Minute_Offset_ofSeconds(v_offset_385_);
    lean_dec(v_offset_385_);
    return v_res_386_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toHours(
    mut v_offset_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_388_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_389_ = lean_int_div(v_offset_387_, v___x_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_Time_Minute_Offset_toHours___boxed(
    mut v_offset_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_391_: *mut LeanObject = core::ptr::null_mut();
    v_res_391_ = l_Std_Time_Minute_Offset_toHours(v_offset_390_);
    lean_dec(v_offset_390_);
    return v_res_391_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofHours(
    mut v_offset_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_393_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_394_ = lean_int_mul(v_offset_392_, v___x_393_);
    return v___x_394_;
}
pub unsafe fn l_Std_Time_Minute_Offset_ofHours___boxed(
    mut v_offset_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_396_: *mut LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Std_Time_Minute_Offset_ofHours(v_offset_395_);
    lean_dec(v_offset_395_);
    return v_res_396_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toNanoseconds(
    mut v_offset_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_399_ = lean_int_mul(v_offset_397_, v___x_398_);
    return v___x_399_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toNanoseconds___boxed(
    mut v_offset_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_401_: *mut LeanObject = core::ptr::null_mut();
    v_res_401_ = l_Std_Time_Hour_Offset_toNanoseconds(v_offset_400_);
    lean_dec(v_offset_400_);
    return v_res_401_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofNanoseconds(
    mut v_offset_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Nanosecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Nanosecond_Offset_toHours___closed__0,
    );
    v___x_404_ = lean_int_div(v_offset_402_, v___x_403_);
    return v___x_404_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofNanoseconds___boxed(
    mut v_offset_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_406_: *mut LeanObject = core::ptr::null_mut();
    v_res_406_ = l_Std_Time_Hour_Offset_ofNanoseconds(v_offset_405_);
    lean_dec(v_offset_405_);
    return v_res_406_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMilliseconds(
    mut v_offset_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    v___x_408_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_409_ = lean_int_mul(v_offset_407_, v___x_408_);
    return v___x_409_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMilliseconds___boxed(
    mut v_offset_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_411_: *mut LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Std_Time_Hour_Offset_toMilliseconds(v_offset_410_);
    lean_dec(v_offset_410_);
    return v_res_411_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMilliseconds(
    mut v_offset_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v___x_413_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Millisecond_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Millisecond_Offset_toHours___closed__0,
    );
    v___x_414_ = lean_int_div(v_offset_412_, v___x_413_);
    return v___x_414_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMilliseconds___boxed(
    mut v_offset_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Time_Hour_Offset_ofMilliseconds(v_offset_415_);
    lean_dec(v_offset_415_);
    return v_res_416_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toSeconds(
    mut v_offset_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_418_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_419_ = lean_int_mul(v_offset_417_, v___x_418_);
    return v___x_419_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toSeconds___boxed(
    mut v_offset_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_421_: *mut LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Std_Time_Hour_Offset_toSeconds(v_offset_420_);
    lean_dec(v_offset_420_);
    return v_res_421_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofSeconds(
    mut v_offset_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toHours___closed__0_once),
        _init_l_Std_Time_Second_Offset_toHours___closed__0,
    );
    v___x_424_ = lean_int_div(v_offset_422_, v___x_423_);
    return v___x_424_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofSeconds___boxed(
    mut v_offset_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_426_: *mut LeanObject = core::ptr::null_mut();
    v_res_426_ = l_Std_Time_Hour_Offset_ofSeconds(v_offset_425_);
    lean_dec(v_offset_425_);
    return v_res_426_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMinutes(
    mut v_offset_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_428_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_429_ = lean_int_mul(v_offset_427_, v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_Std_Time_Hour_Offset_toMinutes___boxed(
    mut v_offset_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_431_: *mut LeanObject = core::ptr::null_mut();
    v_res_431_ = l_Std_Time_Hour_Offset_toMinutes(v_offset_430_);
    lean_dec(v_offset_430_);
    return v_res_431_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMinutes(
    mut v_offset_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Second_Offset_toMinutes___closed__0_once),
        _init_l_Std_Time_Second_Offset_toMinutes___closed__0,
    );
    v___x_434_ = lean_int_div(v_offset_432_, v___x_433_);
    return v___x_434_;
}
pub unsafe fn l_Std_Time_Hour_Offset_ofMinutes___boxed(
    mut v_offset_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_436_: *mut LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Time_Hour_Offset_ofMinutes(v_offset_435_);
    lean_dec(v_offset_435_);
    return v_res_436_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Time_Unit_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Time_Unit_Hour(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Millisecond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Time_Unit_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Time_Unit_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Time_Unit_Hour(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Time_Unit_Millisecond(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Time_Unit_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Time_Unit_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Time_Unit_Basic(builtin);
}
