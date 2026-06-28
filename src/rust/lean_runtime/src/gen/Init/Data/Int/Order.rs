// Lean compiler output
// Module: Init.Data.Int.Order
// Imports: Init.Data.Order.Lemmas Init.Data.Order.Classes Init.NotationExtra Init.ByCases Init.Data.Int.Lemmas
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
pub static mut l_Int_instTransLe: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Int_instTransLtLe: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Int_instTransLeLt: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Int_instTransLt: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_instTransLe() -> *mut LeanObject {
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    v___x_191_ = lean_box(0);
    return v___x_191_;
}
pub unsafe fn _init_l_Int_instTransLtLe() -> *mut LeanObject {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_192_ = lean_box(0);
    return v___x_192_;
}
pub unsafe fn _init_l_Int_instTransLeLt() -> *mut LeanObject {
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    v___x_193_ = lean_box(0);
    return v___x_193_;
}
pub unsafe fn _init_l_Int_instTransLt() -> *mut LeanObject {
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    v___x_194_ = lean_box(0);
    return v___x_194_;
}
pub unsafe fn _init_l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_196_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_195_ = lean_unsigned_to_nat(0);
    v_intZero_196_ = lean_nat_to_int(v_natZero_195_);
    return v_intZero_196_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg(
    mut v_m_197_: *mut LeanObject,
    mut v_n_198_: *mut LeanObject,
    mut v_h__1_199_: *mut LeanObject,
    mut v_h__2_200_: *mut LeanObject,
    mut v_h__3_201_: *mut LeanObject,
    mut v_h__4_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_204_: u8 = 0;
    v_intZero_203_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0_once
        ),
        _init_l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0,
    );
    v_isNeg_204_ = lean_int_dec_lt(v_m_197_, v_intZero_203_);
    if v_isNeg_204_ == 0 {
        let mut v_a_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_206_: u8 = 0;
        lean_dec(v_h__4_202_);
        lean_dec(v_h__3_201_);
        v_a_205_ = lean_nat_abs(v_m_197_);
        v_isNeg_206_ = lean_int_dec_lt(v_n_198_, v_intZero_203_);
        if v_isNeg_206_ == 0 {
            let mut v_a_207_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_200_);
            v_a_207_ = lean_nat_abs(v_n_198_);
            v___x_208_ = lean_apply_2(v_h__1_199_, v_a_205_, v_a_207_);
            return v___x_208_;
        } else {
            let mut v_abs_209_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_210_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_211_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_199_);
            v_abs_209_ = lean_nat_abs(v_n_198_);
            v_one_210_ = lean_unsigned_to_nat(1);
            v_a_211_ = lean_nat_sub(v_abs_209_, v_one_210_);
            lean_dec(v_abs_209_);
            v___x_212_ = lean_apply_2(v_h__2_200_, v_a_205_, v_a_211_);
            return v___x_212_;
        }
    } else {
        let mut v_abs_213_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_214_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_215_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_216_: u8 = 0;
        lean_dec(v_h__2_200_);
        lean_dec(v_h__1_199_);
        v_abs_213_ = lean_nat_abs(v_m_197_);
        v_one_214_ = lean_unsigned_to_nat(1);
        v_a_215_ = lean_nat_sub(v_abs_213_, v_one_214_);
        lean_dec(v_abs_213_);
        v_isNeg_216_ = lean_int_dec_lt(v_n_198_, v_intZero_203_);
        if v_isNeg_216_ == 0 {
            let mut v_a_217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_202_);
            v_a_217_ = lean_nat_abs(v_n_198_);
            v___x_218_ = lean_apply_2(v_h__3_201_, v_a_215_, v_a_217_);
            return v___x_218_;
        } else {
            let mut v_abs_219_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_201_);
            v_abs_219_ = lean_nat_abs(v_n_198_);
            v_a_220_ = lean_nat_sub(v_abs_219_, v_one_214_);
            lean_dec(v_abs_219_);
            v___x_221_ = lean_apply_2(v_h__4_202_, v_a_215_, v_a_220_);
            return v___x_221_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___boxed(
    mut v_m_222_: *mut LeanObject,
    mut v_n_223_: *mut LeanObject,
    mut v_h__1_224_: *mut LeanObject,
    mut v_h__2_225_: *mut LeanObject,
    mut v_h__3_226_: *mut LeanObject,
    mut v_h__4_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_228_: *mut LeanObject = core::ptr::null_mut();
    v_res_228_ = l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg(
        v_m_222_,
        v_n_223_,
        v_h__1_224_,
        v_h__2_225_,
        v_h__3_226_,
        v_h__4_227_,
    );
    lean_dec(v_n_223_);
    lean_dec(v_m_222_);
    return v_res_228_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter(
    mut v_motive_229_: *mut LeanObject,
    mut v_m_230_: *mut LeanObject,
    mut v_n_231_: *mut LeanObject,
    mut v_h__1_232_: *mut LeanObject,
    mut v_h__2_233_: *mut LeanObject,
    mut v_h__3_234_: *mut LeanObject,
    mut v_h__4_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_237_: u8 = 0;
    v_intZero_236_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0_once
        ),
        _init_l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___redArg___closed__0,
    );
    v_isNeg_237_ = lean_int_dec_lt(v_m_230_, v_intZero_236_);
    if v_isNeg_237_ == 0 {
        let mut v_a_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_239_: u8 = 0;
        lean_dec(v_h__4_235_);
        lean_dec(v_h__3_234_);
        v_a_238_ = lean_nat_abs(v_m_230_);
        v_isNeg_239_ = lean_int_dec_lt(v_n_231_, v_intZero_236_);
        if v_isNeg_239_ == 0 {
            let mut v_a_240_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_233_);
            v_a_240_ = lean_nat_abs(v_n_231_);
            v___x_241_ = lean_apply_2(v_h__1_232_, v_a_238_, v_a_240_);
            return v___x_241_;
        } else {
            let mut v_abs_242_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_243_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_232_);
            v_abs_242_ = lean_nat_abs(v_n_231_);
            v_one_243_ = lean_unsigned_to_nat(1);
            v_a_244_ = lean_nat_sub(v_abs_242_, v_one_243_);
            lean_dec(v_abs_242_);
            v___x_245_ = lean_apply_2(v_h__2_233_, v_a_238_, v_a_244_);
            return v___x_245_;
        }
    } else {
        let mut v_abs_246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_247_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_248_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_249_: u8 = 0;
        lean_dec(v_h__2_233_);
        lean_dec(v_h__1_232_);
        v_abs_246_ = lean_nat_abs(v_m_230_);
        v_one_247_ = lean_unsigned_to_nat(1);
        v_a_248_ = lean_nat_sub(v_abs_246_, v_one_247_);
        lean_dec(v_abs_246_);
        v_isNeg_249_ = lean_int_dec_lt(v_n_231_, v_intZero_236_);
        if v_isNeg_249_ == 0 {
            let mut v_a_250_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_235_);
            v_a_250_ = lean_nat_abs(v_n_231_);
            v___x_251_ = lean_apply_2(v_h__3_234_, v_a_248_, v_a_250_);
            return v___x_251_;
        } else {
            let mut v_abs_252_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_253_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_234_);
            v_abs_252_ = lean_nat_abs(v_n_231_);
            v_a_253_ = lean_nat_sub(v_abs_252_, v_one_247_);
            lean_dec(v_abs_252_);
            v___x_254_ = lean_apply_2(v_h__4_235_, v_a_248_, v_a_253_);
            return v___x_254_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter___boxed(
    mut v_motive_255_: *mut LeanObject,
    mut v_m_256_: *mut LeanObject,
    mut v_n_257_: *mut LeanObject,
    mut v_h__1_258_: *mut LeanObject,
    mut v_h__2_259_: *mut LeanObject,
    mut v_h__3_260_: *mut LeanObject,
    mut v_h__4_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_262_: *mut LeanObject = core::ptr::null_mut();
    v_res_262_ = l___private_Init_Data_Int_Order_0__Int_add_match__1_splitter(
        v_motive_255_,
        v_m_256_,
        v_n_257_,
        v_h__1_258_,
        v_h__2_259_,
        v_h__3_260_,
        v_h__4_261_,
    );
    lean_dec(v_n_257_);
    lean_dec(v_m_256_);
    return v_res_262_;
}
pub unsafe fn _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_264_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_263_ = lean_unsigned_to_nat(0);
    v_intZero_264_ = lean_nat_to_int(v_natZero_263_);
    return v_intZero_264_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(
    mut v_n_265_: *mut LeanObject,
    mut v_h__1_266_: *mut LeanObject,
    mut v_h__2_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_269_: u8 = 0;
    v_intZero_268_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once
        ),
        _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0,
    );
    v_isNeg_269_ = lean_int_dec_lt(v_n_265_, v_intZero_268_);
    if v_isNeg_269_ == 0 {
        let mut v_a_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_267_);
        v_a_270_ = lean_nat_abs(v_n_265_);
        v___x_271_ = lean_apply_1(v_h__1_266_, v_a_270_);
        return v___x_271_;
    } else {
        let mut v_abs_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_273_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_266_);
        v_abs_272_ = lean_nat_abs(v_n_265_);
        v_one_273_ = lean_unsigned_to_nat(1);
        v_a_274_ = lean_nat_sub(v_abs_272_, v_one_273_);
        lean_dec(v_abs_272_);
        v___x_275_ = lean_apply_1(v_h__2_267_, v_a_274_);
        return v___x_275_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___boxed(
    mut v_n_276_: *mut LeanObject,
    mut v_h__1_277_: *mut LeanObject,
    mut v_h__2_278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_279_: *mut LeanObject = core::ptr::null_mut();
    v_res_279_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg(
        v_n_276_,
        v_h__1_277_,
        v_h__2_278_,
    );
    lean_dec(v_n_276_);
    return v_res_279_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(
    mut v_motive_280_: *mut LeanObject,
    mut v_n_281_: *mut LeanObject,
    mut v_h__1_282_: *mut LeanObject,
    mut v_h__2_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_285_: u8 = 0;
    v_intZero_284_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0_once
        ),
        _init_l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___redArg___closed__0,
    );
    v_isNeg_285_ = lean_int_dec_lt(v_n_281_, v_intZero_284_);
    if v_isNeg_285_ == 0 {
        let mut v_a_286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_283_);
        v_a_286_ = lean_nat_abs(v_n_281_);
        v___x_287_ = lean_apply_1(v_h__1_282_, v_a_286_);
        return v___x_287_;
    } else {
        let mut v_abs_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_289_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_290_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_282_);
        v_abs_288_ = lean_nat_abs(v_n_281_);
        v_one_289_ = lean_unsigned_to_nat(1);
        v_a_290_ = lean_nat_sub(v_abs_288_, v_one_289_);
        lean_dec(v_abs_288_);
        v___x_291_ = lean_apply_1(v_h__2_283_, v_a_290_);
        return v___x_291_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter___boxed(
    mut v_motive_292_: *mut LeanObject,
    mut v_n_293_: *mut LeanObject,
    mut v_h__1_294_: *mut LeanObject,
    mut v_h__2_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_296_: *mut LeanObject = core::ptr::null_mut();
    v_res_296_ = l___private_Init_Data_Int_Order_0__Int_neg_match__1_splitter(
        v_motive_292_,
        v_n_293_,
        v_h__1_294_,
        v_h__2_295_,
    );
    lean_dec(v_n_293_);
    return v_res_296_;
}
pub unsafe fn _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_298_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_297_ = lean_unsigned_to_nat(0);
    v_intZero_298_ = lean_nat_to_int(v_natZero_297_);
    return v_intZero_298_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(
    mut v_x_299_: *mut LeanObject,
    mut v_h__1_300_: *mut LeanObject,
    mut v_h__2_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_303_: u8 = 0;
    v_intZero_302_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0);
    v_isNeg_303_ = lean_int_dec_lt(v_x_299_, v_intZero_302_);
    if v_isNeg_303_ == 0 {
        let mut v_a_304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_301_);
        v_a_304_ = lean_nat_abs(v_x_299_);
        v___x_305_ = lean_apply_1(v_h__1_300_, v_a_304_);
        return v___x_305_;
    } else {
        let mut v_abs_306_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_300_);
        v_abs_306_ = lean_nat_abs(v_x_299_);
        v_one_307_ = lean_unsigned_to_nat(1);
        v_a_308_ = lean_nat_sub(v_abs_306_, v_one_307_);
        lean_dec(v_abs_306_);
        v___x_309_ = lean_apply_1(v_h__2_301_, v_a_308_);
        return v___x_309_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___boxed(
    mut v_x_310_: *mut LeanObject,
    mut v_h__1_311_: *mut LeanObject,
    mut v_h__2_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_313_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg(
        v_x_310_,
        v_h__1_311_,
        v_h__2_312_,
    );
    lean_dec(v_x_310_);
    return v_res_313_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(
    mut v_motive_314_: *mut LeanObject,
    mut v_x_315_: *mut LeanObject,
    mut v_h__1_316_: *mut LeanObject,
    mut v_h__2_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_319_: u8 = 0;
    v_intZero_318_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___redArg___closed__0);
    v_isNeg_319_ = lean_int_dec_lt(v_x_315_, v_intZero_318_);
    if v_isNeg_319_ == 0 {
        let mut v_a_320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_317_);
        v_a_320_ = lean_nat_abs(v_x_315_);
        v___x_321_ = lean_apply_1(v_h__1_316_, v_a_320_);
        return v___x_321_;
    } else {
        let mut v_abs_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_323_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_316_);
        v_abs_322_ = lean_nat_abs(v_x_315_);
        v_one_323_ = lean_unsigned_to_nat(1);
        v_a_324_ = lean_nat_sub(v_abs_322_, v_one_323_);
        lean_dec(v_abs_322_);
        v___x_325_ = lean_apply_1(v_h__2_317_, v_a_324_);
        return v___x_325_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter___boxed(
    mut v_motive_326_: *mut LeanObject,
    mut v_x_327_: *mut LeanObject,
    mut v_h__1_328_: *mut LeanObject,
    mut v_h__2_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_330_: *mut LeanObject = core::ptr::null_mut();
    v_res_330_ = l___private_Init_Data_Int_Order_0__Int_toNat_match__1_splitter(
        v_motive_326_,
        v_x_327_,
        v_h__1_328_,
        v_h__2_329_,
    );
    lean_dec(v_x_327_);
    return v_res_330_;
}
pub unsafe fn _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_332_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_331_ = lean_unsigned_to_nat(0);
    v_intZero_332_ = lean_nat_to_int(v_natZero_331_);
    return v_intZero_332_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(
    mut v_x_333_: *mut LeanObject,
    mut v_h__1_334_: *mut LeanObject,
    mut v_h__2_335_: *mut LeanObject,
    mut v_h__3_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_339_: u8 = 0;
    v_natZero_337_ = lean_unsigned_to_nat(0);
    v_intZero_338_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once
        ),
        _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0,
    );
    v_isNeg_339_ = lean_int_dec_lt(v_x_333_, v_intZero_338_);
    if v_isNeg_339_ == 0 {
        let mut v_a_340_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_341_: u8 = 0;
        lean_dec(v_h__3_336_);
        v_a_340_ = lean_nat_abs(v_x_333_);
        v_isZero_341_ = lean_nat_dec_eq(v_a_340_, v_natZero_337_);
        if v_isZero_341_ == 1 {
            let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_340_);
            lean_dec(v_h__1_334_);
            v___x_342_ = lean_box(0);
            v___x_343_ = lean_apply_1(v_h__2_335_, v___x_342_);
            return v___x_343_;
        } else {
            let mut v_one_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_335_);
            v_one_344_ = lean_unsigned_to_nat(1);
            v_n_345_ = lean_nat_sub(v_a_340_, v_one_344_);
            lean_dec(v_a_340_);
            v___x_346_ = lean_apply_1(v_h__1_334_, v_n_345_);
            return v___x_346_;
        }
    } else {
        let mut v_abs_347_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_335_);
        lean_dec(v_h__1_334_);
        v_abs_347_ = lean_nat_abs(v_x_333_);
        v_one_348_ = lean_unsigned_to_nat(1);
        v_a_349_ = lean_nat_sub(v_abs_347_, v_one_348_);
        lean_dec(v_abs_347_);
        v___x_350_ = lean_apply_1(v_h__3_336_, v_a_349_);
        return v___x_350_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___boxed(
    mut v_x_351_: *mut LeanObject,
    mut v_h__1_352_: *mut LeanObject,
    mut v_h__2_353_: *mut LeanObject,
    mut v_h__3_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_355_: *mut LeanObject = core::ptr::null_mut();
    v_res_355_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg(
        v_x_351_,
        v_h__1_352_,
        v_h__2_353_,
        v_h__3_354_,
    );
    lean_dec(v_x_351_);
    return v_res_355_;
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(
    mut v_motive_356_: *mut LeanObject,
    mut v_x_357_: *mut LeanObject,
    mut v_h__1_358_: *mut LeanObject,
    mut v_h__2_359_: *mut LeanObject,
    mut v_h__3_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_363_: u8 = 0;
    v_natZero_361_ = lean_unsigned_to_nat(0);
    v_intZero_362_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0_once
        ),
        _init_l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___redArg___closed__0,
    );
    v_isNeg_363_ = lean_int_dec_lt(v_x_357_, v_intZero_362_);
    if v_isNeg_363_ == 0 {
        let mut v_a_364_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_365_: u8 = 0;
        lean_dec(v_h__3_360_);
        v_a_364_ = lean_nat_abs(v_x_357_);
        v_isZero_365_ = lean_nat_dec_eq(v_a_364_, v_natZero_361_);
        if v_isZero_365_ == 1 {
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_364_);
            lean_dec(v_h__1_358_);
            v___x_366_ = lean_box(0);
            v___x_367_ = lean_apply_1(v_h__2_359_, v___x_366_);
            return v___x_367_;
        } else {
            let mut v_one_368_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_359_);
            v_one_368_ = lean_unsigned_to_nat(1);
            v_n_369_ = lean_nat_sub(v_a_364_, v_one_368_);
            lean_dec(v_a_364_);
            v___x_370_ = lean_apply_1(v_h__1_358_, v_n_369_);
            return v___x_370_;
        }
    } else {
        let mut v_abs_371_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_372_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_359_);
        lean_dec(v_h__1_358_);
        v_abs_371_ = lean_nat_abs(v_x_357_);
        v_one_372_ = lean_unsigned_to_nat(1);
        v_a_373_ = lean_nat_sub(v_abs_371_, v_one_372_);
        lean_dec(v_abs_371_);
        v___x_374_ = lean_apply_1(v_h__3_360_, v_a_373_);
        return v___x_374_;
    }
}
pub unsafe fn l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter___boxed(
    mut v_motive_375_: *mut LeanObject,
    mut v_x_376_: *mut LeanObject,
    mut v_h__1_377_: *mut LeanObject,
    mut v_h__2_378_: *mut LeanObject,
    mut v_h__3_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_380_: *mut LeanObject = core::ptr::null_mut();
    v_res_380_ = l___private_Init_Data_Int_Order_0__Int_sign_match__1_splitter(
        v_motive_375_,
        v_x_376_,
        v_h__1_377_,
        v_h__2_378_,
        v_h__3_379_,
    );
    lean_dec(v_x_376_);
    return v_res_380_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Int_instTransLe = _init_l_Int_instTransLe();
    l_Int_instTransLtLe = _init_l_Int_instTransLtLe();
    l_Int_instTransLeLt = _init_l_Int_instTransLeLt();
    l_Int_instTransLt = _init_l_Int_instTransLt();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Order(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Int_Order(builtin);
}
