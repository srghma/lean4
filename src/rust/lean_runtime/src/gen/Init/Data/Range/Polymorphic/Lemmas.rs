// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Lemmas
// Imports: Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Range.Polymorphic.Basic Init.Data.Range.Polymorphic.RangeIterator Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Iterators Init.Data.Iterators.Consumers.Loop Init.Data.Array.Monadic Init.Data.List.Control Init.Data.Order.Lemmas Init.Data.Array.Bootstrap Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Loop Init.Data.List.Pairwise Init.Data.Nat.Linear Init.Omega
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Monadic::{
    initialize_Init_Data_Array_Monadic, runtime_initialize_Init_Data_Array_Monadic,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Loop::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Basic::{
    initialize_Init_Data_Range_Polymorphic_Basic,
    runtime_initialize_Init_Data_Range_Polymorphic_Basic,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::RangeIterator::{
    initialize_Init_Data_Range_Polymorphic_RangeIterator,
    runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(
    mut v_x_171_: *mut LeanObject,
    mut v_h__1_172_: *mut LeanObject,
    mut v_h__2_173_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_173_);
        v___x_174_ = lean_box(0);
        v___x_175_ = lean_apply_1(v_h__1_172_, v___x_174_);
        return v___x_175_;
    } else {
        let mut v_val_176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_172_);
        v_val_176_ = lean_ctor_get(v_x_171_, 0);
        lean_inc(v_val_176_);
        lean_dec_ref_known(v_x_171_, 1);
        v___x_177_ = lean_apply_1(v_h__2_173_, v_val_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter(
    mut v_00_u03b1_178_: *mut LeanObject,
    mut v_motive_179_: *mut LeanObject,
    mut v_x_180_: *mut LeanObject,
    mut v_h__1_181_: *mut LeanObject,
    mut v_h__2_182_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_180_) == 0 {
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_182_);
        v___x_183_ = lean_box(0);
        v___x_184_ = lean_apply_1(v_h__1_181_, v___x_183_);
        return v___x_184_;
    } else {
        let mut v_val_185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_181_);
        v_val_185_ = lean_ctor_get(v_x_180_, 0);
        lean_inc(v_val_185_);
        lean_dec_ref_known(v_x_180_, 1);
        v___x_186_ = lean_apply_1(v_h__2_182_, v_val_185_);
        return v___x_186_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(
    mut v_x_187_: *mut LeanObject,
    mut v_h__1_188_: *mut LeanObject,
    mut v_h__2_189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_187_) == 0 {
        let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_189_);
        v___x_190_ = lean_box(0);
        v___x_191_ = lean_apply_1(v_h__1_188_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_188_);
        v_val_192_ = lean_ctor_get(v_x_187_, 0);
        lean_inc(v_val_192_);
        lean_dec_ref_known(v_x_187_, 1);
        v___x_193_ = lean_apply_1(v_h__2_189_, v_val_192_);
        return v___x_193_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(
    mut v_00_u03b1_194_: *mut LeanObject,
    mut v_motive_195_: *mut LeanObject,
    mut v_x_196_: *mut LeanObject,
    mut v_h__1_197_: *mut LeanObject,
    mut v_h__2_198_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_196_) == 0 {
        let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_198_);
        v___x_199_ = lean_box(0);
        v___x_200_ = lean_apply_1(v_h__1_197_, v___x_199_);
        return v___x_200_;
    } else {
        let mut v_val_201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_197_);
        v_val_201_ = lean_ctor_get(v_x_196_, 0);
        lean_inc(v_val_201_);
        lean_dec_ref_known(v_x_196_, 1);
        v___x_202_ = lean_apply_1(v_h__2_198_, v_val_201_);
        return v___x_202_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_203_: *mut LeanObject,
    mut v_h__1_204_: *mut LeanObject,
    mut v_h__2_205_: *mut LeanObject,
    mut v_h__3_206_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_203_) {
        0 => {
            let mut v_it_207_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_206_);
            lean_dec(v_h__2_205_);
            v_it_207_ = lean_ctor_get(v_x_203_, 0);
            lean_inc(v_it_207_);
            v_out_208_ = lean_ctor_get(v_x_203_, 1);
            lean_inc(v_out_208_);
            lean_dec_ref_known(v_x_203_, 2);
            v___x_209_ = lean_apply_2(v_h__1_204_, v_it_207_, v_out_208_);
            return v___x_209_;
        }
        1 => {
            let mut v_it_210_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_206_);
            lean_dec(v_h__1_204_);
            v_it_210_ = lean_ctor_get(v_x_203_, 0);
            lean_inc(v_it_210_);
            lean_dec_ref_known(v_x_203_, 1);
            v___x_211_ = lean_apply_1(v_h__2_205_, v_it_210_);
            return v___x_211_;
        }
        _ => {
            let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_205_);
            lean_dec(v_h__1_204_);
            v___x_212_ = lean_box(0);
            v___x_213_ = lean_apply_1(v_h__3_206_, v___x_212_);
            return v___x_213_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_214_: *mut LeanObject,
    mut v_00_u03b2_215_: *mut LeanObject,
    mut v_motive_216_: *mut LeanObject,
    mut v_x_217_: *mut LeanObject,
    mut v_h__1_218_: *mut LeanObject,
    mut v_h__2_219_: *mut LeanObject,
    mut v_h__3_220_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_217_) {
        0 => {
            let mut v_it_221_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_220_);
            lean_dec(v_h__2_219_);
            v_it_221_ = lean_ctor_get(v_x_217_, 0);
            lean_inc(v_it_221_);
            v_out_222_ = lean_ctor_get(v_x_217_, 1);
            lean_inc(v_out_222_);
            lean_dec_ref_known(v_x_217_, 2);
            v___x_223_ = lean_apply_2(v_h__1_218_, v_it_221_, v_out_222_);
            return v___x_223_;
        }
        1 => {
            let mut v_it_224_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_220_);
            lean_dec(v_h__1_218_);
            v_it_224_ = lean_ctor_get(v_x_217_, 0);
            lean_inc(v_it_224_);
            lean_dec_ref_known(v_x_217_, 1);
            v___x_225_ = lean_apply_1(v_h__2_219_, v_it_224_);
            return v___x_225_;
        }
        _ => {
            let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_219_);
            lean_dec(v_h__1_218_);
            v___x_226_ = lean_box(0);
            v___x_227_ = lean_apply_1(v_h__3_220_, v___x_226_);
            return v___x_227_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(
    mut v_____do__lift_228_: *mut LeanObject,
    mut v_h__1_229_: *mut LeanObject,
    mut v_h__2_230_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_228_) == 0 {
        let mut v_a_231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_229_);
        v_a_231_ = lean_ctor_get(v_____do__lift_228_, 0);
        lean_inc(v_a_231_);
        lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_232_ = lean_apply_1(v_h__2_230_, v_a_231_);
        return v___x_232_;
    } else {
        let mut v_a_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_230_);
        v_a_233_ = lean_ctor_get(v_____do__lift_228_, 0);
        lean_inc(v_a_233_);
        lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_234_ = lean_apply_1(v_h__1_229_, v_a_233_);
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter(
    mut v_00_u03b3_235_: *mut LeanObject,
    mut v_motive_236_: *mut LeanObject,
    mut v_____do__lift_237_: *mut LeanObject,
    mut v_h__1_238_: *mut LeanObject,
    mut v_h__2_239_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_237_) == 0 {
        let mut v_a_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_238_);
        v_a_240_ = lean_ctor_get(v_____do__lift_237_, 0);
        lean_inc(v_a_240_);
        lean_dec_ref_known(v_____do__lift_237_, 1);
        v___x_241_ = lean_apply_1(v_h__2_239_, v_a_240_);
        return v___x_241_;
    } else {
        let mut v_a_242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_239_);
        v_a_242_ = lean_ctor_get(v_____do__lift_237_, 0);
        lean_inc(v_a_242_);
        lean_dec_ref_known(v_____do__lift_237_, 1);
        v___x_243_ = lean_apply_1(v_h__1_238_, v_a_242_);
        return v___x_243_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_244_: *mut LeanObject,
    mut v_h__1_245_: *mut LeanObject,
    mut v_h__2_246_: *mut LeanObject,
    mut v_h__3_247_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_244_) {
        0 => {
            let mut v_it_248_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_249_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_247_);
            lean_dec(v_h__2_246_);
            v_it_248_ = lean_ctor_get(v_x_244_, 0);
            lean_inc(v_it_248_);
            v_out_249_ = lean_ctor_get(v_x_244_, 1);
            lean_inc(v_out_249_);
            lean_dec_ref_known(v_x_244_, 2);
            v___x_250_ = lean_apply_3(v_h__1_245_, v_it_248_, v_out_249_, lean_box(0));
            return v___x_250_;
        }
        1 => {
            let mut v_it_251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_247_);
            lean_dec(v_h__1_245_);
            v_it_251_ = lean_ctor_get(v_x_244_, 0);
            lean_inc(v_it_251_);
            lean_dec_ref_known(v_x_244_, 1);
            v___x_252_ = lean_apply_2(v_h__2_246_, v_it_251_, lean_box(0));
            return v___x_252_;
        }
        _ => {
            let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_246_);
            lean_dec(v_h__1_245_);
            v___x_253_ = lean_apply_1(v_h__3_247_, lean_box(0));
            return v___x_253_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_254_: *mut LeanObject,
    mut v_00_u03b2_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
    mut v_it_257_: *mut LeanObject,
    mut v_motive_258_: *mut LeanObject,
    mut v_x_259_: *mut LeanObject,
    mut v_h__1_260_: *mut LeanObject,
    mut v_h__2_261_: *mut LeanObject,
    mut v_h__3_262_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_259_) {
        0 => {
            let mut v_it_263_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_264_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_262_);
            lean_dec(v_h__2_261_);
            v_it_263_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_it_263_);
            v_out_264_ = lean_ctor_get(v_x_259_, 1);
            lean_inc(v_out_264_);
            lean_dec_ref_known(v_x_259_, 2);
            v___x_265_ = lean_apply_3(v_h__1_260_, v_it_263_, v_out_264_, lean_box(0));
            return v___x_265_;
        }
        1 => {
            let mut v_it_266_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_262_);
            lean_dec(v_h__1_260_);
            v_it_266_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_it_266_);
            lean_dec_ref_known(v_x_259_, 1);
            v___x_267_ = lean_apply_2(v_h__2_261_, v_it_266_, lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_261_);
            lean_dec(v_h__1_260_);
            v___x_268_ = lean_apply_1(v_h__3_262_, lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_269_: *mut LeanObject,
    mut v_00_u03b2_270_: *mut LeanObject,
    mut v_inst_271_: *mut LeanObject,
    mut v_it_272_: *mut LeanObject,
    mut v_motive_273_: *mut LeanObject,
    mut v_x_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
    mut v_h__3_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_269_, v_00_u03b2_270_, v_inst_271_, v_it_272_, v_motive_273_, v_x_274_, v_h__1_275_, v_h__2_276_, v_h__3_277_);
    lean_dec(v_it_272_);
    lean_dec(v_inst_271_);
    return v_res_278_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_279_: *mut LeanObject,
    mut v_h__1_280_: *mut LeanObject,
    mut v_h__2_281_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_279_) == 0 {
        let mut v_a_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_280_);
        v_a_282_ = lean_ctor_get(v_____do__lift_279_, 0);
        lean_inc(v_a_282_);
        lean_dec_ref_known(v_____do__lift_279_, 1);
        v___x_283_ = lean_apply_1(v_h__2_281_, v_a_282_);
        return v___x_283_;
    } else {
        let mut v_a_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_281_);
        v_a_284_ = lean_ctor_get(v_____do__lift_279_, 0);
        lean_inc(v_a_284_);
        lean_dec_ref_known(v_____do__lift_279_, 1);
        v___x_285_ = lean_apply_1(v_h__1_280_, v_a_284_);
        return v___x_285_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_286_: *mut LeanObject,
    mut v_motive_287_: *mut LeanObject,
    mut v_____do__lift_288_: *mut LeanObject,
    mut v_h__1_289_: *mut LeanObject,
    mut v_h__2_290_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_288_) == 0 {
        let mut v_a_291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_289_);
        v_a_291_ = lean_ctor_get(v_____do__lift_288_, 0);
        lean_inc(v_a_291_);
        lean_dec_ref_known(v_____do__lift_288_, 1);
        v___x_292_ = lean_apply_1(v_h__2_290_, v_a_291_);
        return v___x_292_;
    } else {
        let mut v_a_293_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_290_);
        v_a_293_ = lean_ctor_get(v_____do__lift_288_, 0);
        lean_inc(v_a_293_);
        lean_dec_ref_known(v_____do__lift_288_, 1);
        v___x_294_ = lean_apply_1(v_h__1_289_, v_a_293_);
        return v___x_294_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(
    mut v_x_295_: *mut LeanObject,
    mut v_h__1_296_: *mut LeanObject,
    mut v_h__2_297_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_295_) == 0 {
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_297_);
        v___x_298_ = lean_apply_1(v_h__1_296_, lean_box(0));
        return v___x_298_;
    } else {
        let mut v_val_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_296_);
        v_val_299_ = lean_ctor_get(v_x_295_, 0);
        lean_inc(v_val_299_);
        lean_dec_ref_known(v_x_295_, 1);
        v___x_300_ = lean_apply_2(v_h__2_297_, v_val_299_, lean_box(0));
        return v___x_300_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter(
    mut v_00_u03b1_301_: *mut LeanObject,
    mut v_motive_302_: *mut LeanObject,
    mut v_x_303_: *mut LeanObject,
    mut v_h__1_304_: *mut LeanObject,
    mut v_h__2_305_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_303_) == 0 {
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_305_);
        v___x_306_ = lean_apply_1(v_h__1_304_, lean_box(0));
        return v___x_306_;
    } else {
        let mut v_val_307_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_304_);
        v_val_307_ = lean_ctor_get(v_x_303_, 0);
        lean_inc(v_val_307_);
        lean_dec_ref_known(v_x_303_, 1);
        v___x_308_ = lean_apply_2(v_h__2_305_, v_val_307_, lean_box(0));
        return v___x_308_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_309_: *mut LeanObject,
    mut v_h__1_310_: *mut LeanObject,
    mut v_h__2_311_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_309_) == 0 {
        let mut v_a_312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_311_);
        v_a_312_ = lean_ctor_get(v_x_309_, 0);
        lean_inc(v_a_312_);
        lean_dec_ref_known(v_x_309_, 1);
        v___x_313_ = lean_apply_1(v_h__1_310_, v_a_312_);
        return v___x_313_;
    } else {
        let mut v_a_314_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_310_);
        v_a_314_ = lean_ctor_get(v_x_309_, 0);
        lean_inc(v_a_314_);
        lean_dec_ref_known(v_x_309_, 1);
        v___x_315_ = lean_apply_1(v_h__2_311_, v_a_314_);
        return v___x_315_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_316_: *mut LeanObject,
    mut v_motive_317_: *mut LeanObject,
    mut v_x_318_: *mut LeanObject,
    mut v_h__1_319_: *mut LeanObject,
    mut v_h__2_320_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_318_) == 0 {
        let mut v_a_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_320_);
        v_a_321_ = lean_ctor_get(v_x_318_, 0);
        lean_inc(v_a_321_);
        lean_dec_ref_known(v_x_318_, 1);
        v___x_322_ = lean_apply_1(v_h__1_319_, v_a_321_);
        return v___x_322_;
    } else {
        let mut v_a_323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_319_);
        v_a_323_ = lean_ctor_get(v_x_318_, 0);
        lean_inc(v_a_323_);
        lean_dec_ref_known(v_x_318_, 1);
        v___x_324_ = lean_apply_1(v_h__2_320_, v_a_323_);
        return v___x_324_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(
    mut v_x_325_: *mut LeanObject,
    mut v_h__1_326_: *mut LeanObject,
    mut v_h__2_327_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_325_) == 0 {
        let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_327_);
        v___x_328_ = lean_box(0);
        v___x_329_ = lean_apply_1(v_h__1_326_, v___x_328_);
        return v___x_329_;
    } else {
        let mut v_val_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_326_);
        v_val_330_ = lean_ctor_get(v_x_325_, 0);
        lean_inc(v_val_330_);
        lean_dec_ref_known(v_x_325_, 1);
        v___x_331_ = lean_apply_1(v_h__2_327_, v_val_330_);
        return v___x_331_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter(
    mut v_00_u03b1_332_: *mut LeanObject,
    mut v_motive_333_: *mut LeanObject,
    mut v_x_334_: *mut LeanObject,
    mut v_h__1_335_: *mut LeanObject,
    mut v_h__2_336_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_334_) == 0 {
        let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_336_);
        v___x_337_ = lean_box(0);
        v___x_338_ = lean_apply_1(v_h__1_335_, v___x_337_);
        return v___x_338_;
    } else {
        let mut v_val_339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_335_);
        v_val_339_ = lean_ctor_get(v_x_334_, 0);
        lean_inc(v_val_339_);
        lean_dec_ref_known(v_x_334_, 1);
        v___x_340_ = lean_apply_1(v_h__2_336_, v_val_339_);
        return v___x_340_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
}
