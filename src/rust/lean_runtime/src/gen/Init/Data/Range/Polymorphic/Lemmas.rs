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
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter___redArg(
    mut v_x_171_: *mut crate::leanh::LeanObject,
    mut v_h__1_172_: *mut crate::leanh::LeanObject,
    mut v_h__2_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_171_) == 0 {
        let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_173_);
        v___x_174_ = crate::leanh::lean_box(0);
        v___x_175_ = crate::leanh::lean_apply_1(v_h__1_172_, v___x_174_);
        return v___x_175_;
    } else {
        let mut v_val_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_172_);
        v_val_176_ = crate::leanh::lean_ctor_get(v_x_171_, 0);
        crate::leanh::lean_inc(v_val_176_);
        crate::leanh::lean_dec_ref_known(v_x_171_, 1);
        v___x_177_ = crate::leanh::lean_apply_1(v_h__2_173_, v_val_176_);
        return v___x_177_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_toList__eq__match_match__1_splitter(
    mut v_00_u03b1_178_: *mut crate::leanh::LeanObject,
    mut v_motive_179_: *mut crate::leanh::LeanObject,
    mut v_x_180_: *mut crate::leanh::LeanObject,
    mut v_h__1_181_: *mut crate::leanh::LeanObject,
    mut v_h__2_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_180_) == 0 {
        let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_182_);
        v___x_183_ = crate::leanh::lean_box(0);
        v___x_184_ = crate::leanh::lean_apply_1(v_h__1_181_, v___x_183_);
        return v___x_184_;
    } else {
        let mut v_val_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_181_);
        v_val_185_ = crate::leanh::lean_ctor_get(v_x_180_, 0);
        crate::leanh::lean_inc(v_val_185_);
        crate::leanh::lean_dec_ref_known(v_x_180_, 1);
        v___x_186_ = crate::leanh::lean_apply_1(v_h__2_182_, v_val_185_);
        return v___x_186_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(
    mut v_x_187_: *mut crate::leanh::LeanObject,
    mut v_h__1_188_: *mut crate::leanh::LeanObject,
    mut v_h__2_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_187_) == 0 {
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_189_);
        v___x_190_ = crate::leanh::lean_box(0);
        v___x_191_ = crate::leanh::lean_apply_1(v_h__1_188_, v___x_190_);
        return v___x_191_;
    } else {
        let mut v_val_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_188_);
        v_val_192_ = crate::leanh::lean_ctor_get(v_x_187_, 0);
        crate::leanh::lean_inc(v_val_192_);
        crate::leanh::lean_dec_ref_known(v_x_187_, 1);
        v___x_193_ = crate::leanh::lean_apply_1(v_h__2_189_, v_val_192_);
        return v___x_193_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(
    mut v_00_u03b1_194_: *mut crate::leanh::LeanObject,
    mut v_motive_195_: *mut crate::leanh::LeanObject,
    mut v_x_196_: *mut crate::leanh::LeanObject,
    mut v_h__1_197_: *mut crate::leanh::LeanObject,
    mut v_h__2_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_196_) == 0 {
        let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_198_);
        v___x_199_ = crate::leanh::lean_box(0);
        v___x_200_ = crate::leanh::lean_apply_1(v_h__1_197_, v___x_199_);
        return v___x_200_;
    } else {
        let mut v_val_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_197_);
        v_val_201_ = crate::leanh::lean_ctor_get(v_x_196_, 0);
        crate::leanh::lean_inc(v_val_201_);
        crate::leanh::lean_dec_ref_known(v_x_196_, 1);
        v___x_202_ = crate::leanh::lean_apply_1(v_h__2_198_, v_val_201_);
        return v___x_202_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_203_: *mut crate::leanh::LeanObject,
    mut v_h__1_204_: *mut crate::leanh::LeanObject,
    mut v_h__2_205_: *mut crate::leanh::LeanObject,
    mut v_h__3_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_203_) {
        0 => {
            let mut v_it_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_206_);
            crate::leanh::lean_dec(v_h__2_205_);
            v_it_207_ = crate::leanh::lean_ctor_get(v_x_203_, 0);
            crate::leanh::lean_inc(v_it_207_);
            v_out_208_ = crate::leanh::lean_ctor_get(v_x_203_, 1);
            crate::leanh::lean_inc(v_out_208_);
            crate::leanh::lean_dec_ref_known(v_x_203_, 2);
            v___x_209_ = crate::leanh::lean_apply_2(v_h__1_204_, v_it_207_, v_out_208_);
            return v___x_209_;
        }
        1 => {
            let mut v_it_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_206_);
            crate::leanh::lean_dec(v_h__1_204_);
            v_it_210_ = crate::leanh::lean_ctor_get(v_x_203_, 0);
            crate::leanh::lean_inc(v_it_210_);
            crate::leanh::lean_dec_ref_known(v_x_203_, 1);
            v___x_211_ = crate::leanh::lean_apply_1(v_h__2_205_, v_it_210_);
            return v___x_211_;
        }
        _ => {
            let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_205_);
            crate::leanh::lean_dec(v_h__1_204_);
            v___x_212_ = crate::leanh::lean_box(0);
            v___x_213_ = crate::leanh::lean_apply_1(v_h__3_206_, v___x_212_);
            return v___x_213_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_214_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_215_: *mut crate::leanh::LeanObject,
    mut v_motive_216_: *mut crate::leanh::LeanObject,
    mut v_x_217_: *mut crate::leanh::LeanObject,
    mut v_h__1_218_: *mut crate::leanh::LeanObject,
    mut v_h__2_219_: *mut crate::leanh::LeanObject,
    mut v_h__3_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_217_) {
        0 => {
            let mut v_it_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_220_);
            crate::leanh::lean_dec(v_h__2_219_);
            v_it_221_ = crate::leanh::lean_ctor_get(v_x_217_, 0);
            crate::leanh::lean_inc(v_it_221_);
            v_out_222_ = crate::leanh::lean_ctor_get(v_x_217_, 1);
            crate::leanh::lean_inc(v_out_222_);
            crate::leanh::lean_dec_ref_known(v_x_217_, 2);
            v___x_223_ = crate::leanh::lean_apply_2(v_h__1_218_, v_it_221_, v_out_222_);
            return v___x_223_;
        }
        1 => {
            let mut v_it_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_220_);
            crate::leanh::lean_dec(v_h__1_218_);
            v_it_224_ = crate::leanh::lean_ctor_get(v_x_217_, 0);
            crate::leanh::lean_inc(v_it_224_);
            crate::leanh::lean_dec_ref_known(v_x_217_, 1);
            v___x_225_ = crate::leanh::lean_apply_1(v_h__2_219_, v_it_224_);
            return v___x_225_;
        }
        _ => {
            let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_219_);
            crate::leanh::lean_dec(v_h__1_218_);
            v___x_226_ = crate::leanh::lean_box(0);
            v___x_227_ = crate::leanh::lean_apply_1(v_h__3_220_, v___x_226_);
            return v___x_227_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter___redArg(
    mut v_____do__lift_228_: *mut crate::leanh::LeanObject,
    mut v_h__1_229_: *mut crate::leanh::LeanObject,
    mut v_h__2_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_228_) == 0 {
        let mut v_a_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_229_);
        v_a_231_ = crate::leanh::lean_ctor_get(v_____do__lift_228_, 0);
        crate::leanh::lean_inc(v_a_231_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_232_ = crate::leanh::lean_apply_1(v_h__2_230_, v_a_231_);
        return v___x_232_;
    } else {
        let mut v_a_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_230_);
        v_a_233_ = crate::leanh::lean_ctor_get(v_____do__lift_228_, 0);
        crate::leanh::lean_inc(v_a_233_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_228_, 1);
        v___x_234_ = crate::leanh::lean_apply_1(v_h__1_229_, v_a_233_);
        return v___x_234_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Rcc_forIn_x27__eq__if_match__1_splitter(
    mut v_00_u03b3_235_: *mut crate::leanh::LeanObject,
    mut v_motive_236_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_237_: *mut crate::leanh::LeanObject,
    mut v_h__1_238_: *mut crate::leanh::LeanObject,
    mut v_h__2_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_237_) == 0 {
        let mut v_a_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_238_);
        v_a_240_ = crate::leanh::lean_ctor_get(v_____do__lift_237_, 0);
        crate::leanh::lean_inc(v_a_240_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_237_, 1);
        v___x_241_ = crate::leanh::lean_apply_1(v_h__2_239_, v_a_240_);
        return v___x_241_;
    } else {
        let mut v_a_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_239_);
        v_a_242_ = crate::leanh::lean_ctor_get(v_____do__lift_237_, 0);
        crate::leanh::lean_inc(v_a_242_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_237_, 1);
        v___x_243_ = crate::leanh::lean_apply_1(v_h__1_238_, v_a_242_);
        return v___x_243_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___redArg(
    mut v_x_244_: *mut crate::leanh::LeanObject,
    mut v_h__1_245_: *mut crate::leanh::LeanObject,
    mut v_h__2_246_: *mut crate::leanh::LeanObject,
    mut v_h__3_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_244_) {
        0 => {
            let mut v_it_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_247_);
            crate::leanh::lean_dec(v_h__2_246_);
            v_it_248_ = crate::leanh::lean_ctor_get(v_x_244_, 0);
            crate::leanh::lean_inc(v_it_248_);
            v_out_249_ = crate::leanh::lean_ctor_get(v_x_244_, 1);
            crate::leanh::lean_inc(v_out_249_);
            crate::leanh::lean_dec_ref_known(v_x_244_, 2);
            v___x_250_ = crate::leanh::lean_apply_3(
                v_h__1_245_,
                v_it_248_,
                v_out_249_,
                crate::leanh::lean_box(0),
            );
            return v___x_250_;
        }
        1 => {
            let mut v_it_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_247_);
            crate::leanh::lean_dec(v_h__1_245_);
            v_it_251_ = crate::leanh::lean_ctor_get(v_x_244_, 0);
            crate::leanh::lean_inc(v_it_251_);
            crate::leanh::lean_dec_ref_known(v_x_244_, 1);
            v___x_252_ =
                crate::leanh::lean_apply_2(v_h__2_246_, v_it_251_, crate::leanh::lean_box(0));
            return v___x_252_;
        }
        _ => {
            let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_246_);
            crate::leanh::lean_dec(v_h__1_245_);
            v___x_253_ = crate::leanh::lean_apply_1(v_h__3_247_, crate::leanh::lean_box(0));
            return v___x_253_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(
    mut v_00_u03b1_254_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
    mut v_it_257_: *mut crate::leanh::LeanObject,
    mut v_motive_258_: *mut crate::leanh::LeanObject,
    mut v_x_259_: *mut crate::leanh::LeanObject,
    mut v_h__1_260_: *mut crate::leanh::LeanObject,
    mut v_h__2_261_: *mut crate::leanh::LeanObject,
    mut v_h__3_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_259_) {
        0 => {
            let mut v_it_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_262_);
            crate::leanh::lean_dec(v_h__2_261_);
            v_it_263_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
            crate::leanh::lean_inc(v_it_263_);
            v_out_264_ = crate::leanh::lean_ctor_get(v_x_259_, 1);
            crate::leanh::lean_inc(v_out_264_);
            crate::leanh::lean_dec_ref_known(v_x_259_, 2);
            v___x_265_ = crate::leanh::lean_apply_3(
                v_h__1_260_,
                v_it_263_,
                v_out_264_,
                crate::leanh::lean_box(0),
            );
            return v___x_265_;
        }
        1 => {
            let mut v_it_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_262_);
            crate::leanh::lean_dec(v_h__1_260_);
            v_it_266_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
            crate::leanh::lean_inc(v_it_266_);
            crate::leanh::lean_dec_ref_known(v_x_259_, 1);
            v___x_267_ =
                crate::leanh::lean_apply_2(v_h__2_261_, v_it_266_, crate::leanh::lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_261_);
            crate::leanh::lean_dec(v_h__1_260_);
            v___x_268_ = crate::leanh::lean_apply_1(v_h__3_262_, crate::leanh::lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter___boxed(
    mut v_00_u03b1_269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
    mut v_it_272_: *mut crate::leanh::LeanObject,
    mut v_motive_273_: *mut crate::leanh::LeanObject,
    mut v_x_274_: *mut crate::leanh::LeanObject,
    mut v_h__1_275_: *mut crate::leanh::LeanObject,
    mut v_h__2_276_: *mut crate::leanh::LeanObject,
    mut v_h__3_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_269_, v_00_u03b2_270_, v_inst_271_, v_it_272_, v_motive_273_, v_x_274_, v_h__1_275_, v_h__2_276_, v_h__3_277_);
    crate::leanh::lean_dec(v_it_272_);
    crate::leanh::lean_dec(v_inst_271_);
    return v_res_278_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter___redArg(
    mut v_____do__lift_279_: *mut crate::leanh::LeanObject,
    mut v_h__1_280_: *mut crate::leanh::LeanObject,
    mut v_h__2_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_279_) == 0 {
        let mut v_a_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_280_);
        v_a_282_ = crate::leanh::lean_ctor_get(v_____do__lift_279_, 0);
        crate::leanh::lean_inc(v_a_282_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_279_, 1);
        v___x_283_ = crate::leanh::lean_apply_1(v_h__2_281_, v_a_282_);
        return v___x_283_;
    } else {
        let mut v_a_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_281_);
        v_a_284_ = crate::leanh::lean_ctor_get(v_____do__lift_279_, 0);
        crate::leanh::lean_inc(v_a_284_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_279_, 1);
        v___x_285_ = crate::leanh::lean_apply_1(v_h__1_280_, v_a_284_);
        return v___x_285_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Iter_forIn_x27__eq__match__step_match__1_splitter(
    mut v_00_u03b3_286_: *mut crate::leanh::LeanObject,
    mut v_motive_287_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_288_: *mut crate::leanh::LeanObject,
    mut v_h__1_289_: *mut crate::leanh::LeanObject,
    mut v_h__2_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_288_) == 0 {
        let mut v_a_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_289_);
        v_a_291_ = crate::leanh::lean_ctor_get(v_____do__lift_288_, 0);
        crate::leanh::lean_inc(v_a_291_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_288_, 1);
        v___x_292_ = crate::leanh::lean_apply_1(v_h__2_290_, v_a_291_);
        return v___x_292_;
    } else {
        let mut v_a_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_290_);
        v_a_293_ = crate::leanh::lean_ctor_get(v_____do__lift_288_, 0);
        crate::leanh::lean_inc(v_a_293_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_288_, 1);
        v___x_294_ = crate::leanh::lean_apply_1(v_h__1_289_, v_a_293_);
        return v___x_294_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter___redArg(
    mut v_x_295_: *mut crate::leanh::LeanObject,
    mut v_h__1_296_: *mut crate::leanh::LeanObject,
    mut v_h__2_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_295_) == 0 {
        let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_297_);
        v___x_298_ = crate::leanh::lean_apply_1(v_h__1_296_, crate::leanh::lean_box(0));
        return v___x_298_;
    } else {
        let mut v_val_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_296_);
        v_val_299_ = crate::leanh::lean_ctor_get(v_x_295_, 0);
        crate::leanh::lean_inc(v_val_299_);
        crate::leanh::lean_dec_ref_known(v_x_295_, 1);
        v___x_300_ = crate::leanh::lean_apply_2(v_h__2_297_, v_val_299_, crate::leanh::lean_box(0));
        return v___x_300_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_forIn_x27__eq__match_match__1_splitter(
    mut v_00_u03b1_301_: *mut crate::leanh::LeanObject,
    mut v_motive_302_: *mut crate::leanh::LeanObject,
    mut v_x_303_: *mut crate::leanh::LeanObject,
    mut v_h__1_304_: *mut crate::leanh::LeanObject,
    mut v_h__2_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_303_) == 0 {
        let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_305_);
        v___x_306_ = crate::leanh::lean_apply_1(v_h__1_304_, crate::leanh::lean_box(0));
        return v___x_306_;
    } else {
        let mut v_val_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_304_);
        v_val_307_ = crate::leanh::lean_ctor_get(v_x_303_, 0);
        crate::leanh::lean_inc(v_val_307_);
        crate::leanh::lean_dec_ref_known(v_x_303_, 1);
        v___x_308_ = crate::leanh::lean_apply_2(v_h__2_305_, v_val_307_, crate::leanh::lean_box(0));
        return v___x_308_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_309_: *mut crate::leanh::LeanObject,
    mut v_h__1_310_: *mut crate::leanh::LeanObject,
    mut v_h__2_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_309_) == 0 {
        let mut v_a_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_311_);
        v_a_312_ = crate::leanh::lean_ctor_get(v_x_309_, 0);
        crate::leanh::lean_inc(v_a_312_);
        crate::leanh::lean_dec_ref_known(v_x_309_, 1);
        v___x_313_ = crate::leanh::lean_apply_1(v_h__1_310_, v_a_312_);
        return v___x_313_;
    } else {
        let mut v_a_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_310_);
        v_a_314_ = crate::leanh::lean_ctor_get(v_x_309_, 0);
        crate::leanh::lean_inc(v_a_314_);
        crate::leanh::lean_dec_ref_known(v_x_309_, 1);
        v___x_315_ = crate::leanh::lean_apply_1(v_h__2_311_, v_a_314_);
        return v___x_315_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_316_: *mut crate::leanh::LeanObject,
    mut v_motive_317_: *mut crate::leanh::LeanObject,
    mut v_x_318_: *mut crate::leanh::LeanObject,
    mut v_h__1_319_: *mut crate::leanh::LeanObject,
    mut v_h__2_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_318_) == 0 {
        let mut v_a_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_320_);
        v_a_321_ = crate::leanh::lean_ctor_get(v_x_318_, 0);
        crate::leanh::lean_inc(v_a_321_);
        crate::leanh::lean_dec_ref_known(v_x_318_, 1);
        v___x_322_ = crate::leanh::lean_apply_1(v_h__1_319_, v_a_321_);
        return v___x_322_;
    } else {
        let mut v_a_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_319_);
        v_a_323_ = crate::leanh::lean_ctor_get(v_x_318_, 0);
        crate::leanh::lean_inc(v_a_323_);
        crate::leanh::lean_dec_ref_known(v_x_318_, 1);
        v___x_324_ = crate::leanh::lean_apply_1(v_h__2_320_, v_a_323_);
        return v___x_324_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter___redArg(
    mut v_x_325_: *mut crate::leanh::LeanObject,
    mut v_h__1_326_: *mut crate::leanh::LeanObject,
    mut v_h__2_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_325_) == 0 {
        let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_327_);
        v___x_328_ = crate::leanh::lean_box(0);
        v___x_329_ = crate::leanh::lean_apply_1(v_h__1_326_, v___x_328_);
        return v___x_329_;
    } else {
        let mut v_val_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_326_);
        v_val_330_ = crate::leanh::lean_ctor_get(v_x_325_, 0);
        crate::leanh::lean_inc(v_val_330_);
        crate::leanh::lean_dec_ref_known(v_x_325_, 1);
        v___x_331_ = crate::leanh::lean_apply_1(v_h__2_327_, v_val_330_);
        return v___x_331_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Lemmas_0__Std_Roc_size_match__1_splitter(
    mut v_00_u03b1_332_: *mut crate::leanh::LeanObject,
    mut v_motive_333_: *mut crate::leanh::LeanObject,
    mut v_x_334_: *mut crate::leanh::LeanObject,
    mut v_h__1_335_: *mut crate::leanh::LeanObject,
    mut v_h__2_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_334_) == 0 {
        let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_336_);
        v___x_337_ = crate::leanh::lean_box(0);
        v___x_338_ = crate::leanh::lean_apply_1(v_h__1_335_, v___x_337_);
        return v___x_338_;
    } else {
        let mut v_val_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_335_);
        v_val_339_ = crate::leanh::lean_ctor_get(v_x_334_, 0);
        crate::leanh::lean_inc(v_val_339_);
        crate::leanh::lean_dec_ref_known(v_x_334_, 1);
        v___x_340_ = crate::leanh::lean_apply_1(v_h__2_336_, v_val_339_);
        return v___x_340_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Lemmas(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
}
