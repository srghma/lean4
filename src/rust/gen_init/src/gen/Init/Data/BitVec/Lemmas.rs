// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: Init.Data.BitVec.Basic Init.Data.BitVec.BasicAux Init.Data.Fin.Lemmas Init.Data.List.BasicAux Init.Data.List.Lemmas Init.Data.BitVec.Basic Init.ByCases Init.Data.BitVec.Bootstrap Init.Data.Int.Bitwise.Lemmas Init.Data.Int.DivMod.Lemmas Init.Data.Int.LemmasAux Init.Data.Int.Pow Init.Data.Nat.Div.Lemmas Init.Data.Nat.MinMax Init.Data.Nat.Mod Init.Data.Nat.Simproc Init.TacticsExtra
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_dec_eq, lean_nat_sub, lean_nat_to_int};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::BasicAux::{
    initialize_Init_Data_BitVec_BasicAux, runtime_initialize_Init_Data_BitVec_BasicAux,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Int::Bitwise::Lemmas::{
    initialize_Init_Data_Int_Bitwise_Lemmas, runtime_initialize_Init_Data_Int_Bitwise_Lemmas,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::List::BasicAux::{
    initialize_Init_Data_List_BasicAux, runtime_initialize_Init_Data_List_BasicAux,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Div::Lemmas::{
    initialize_Init_Data_Nat_Div_Lemmas, runtime_initialize_Init_Data_Nat_Div_Lemmas,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Nat::Mod::{
    initialize_Init_Data_Nat_Mod, runtime_initialize_Init_Data_Nat_Mod,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
static mut l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_166_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_167_ = lean_nat_to_int(v_natZero_166_);
    return v_intZero_167_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(
    mut v_x_168_: *mut leanh::LeanObject,
    mut v_h__1_169_: *mut leanh::LeanObject,
    mut v_h__2_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_172_: u8 = 0;
    v_intZero_171_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
    v_isNeg_172_ = lean_int_dec_lt(v_x_168_, v_intZero_171_);
    if v_isNeg_172_ == 0 {
        let mut v_a_173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_170_);
        v_a_173_ = lean_nat_abs(v_x_168_);
        v___x_174_ = leanh::lean_apply_1(v_h__1_169_, v_a_173_);
        return v___x_174_;
    } else {
        let mut v_abs_175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_169_);
        v_abs_175_ = lean_nat_abs(v_x_168_);
        v_one_176_ = leanh::lean_unsigned_to_nat(1);
        v_a_177_ = lean_nat_sub(v_abs_175_, v_one_176_);
        leanh::lean_dec(v_abs_175_);
        v___x_178_ = leanh::lean_apply_1(v_h__2_170_, v_a_177_);
        return v___x_178_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(
    mut v_x_179_: *mut leanh::LeanObject,
    mut v_h__1_180_: *mut leanh::LeanObject,
    mut v_h__2_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(
        v_x_179_,
        v_h__1_180_,
        v_h__2_181_,
    );
    leanh::lean_dec(v_x_179_);
    return v_res_182_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(
    mut v_motive_183_: *mut leanh::LeanObject,
    mut v_x_184_: *mut leanh::LeanObject,
    mut v_h__1_185_: *mut leanh::LeanObject,
    mut v_h__2_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_188_: u8 = 0;
    v_intZero_187_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
    v_isNeg_188_ = lean_int_dec_lt(v_x_184_, v_intZero_187_);
    if v_isNeg_188_ == 0 {
        let mut v_a_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_186_);
        v_a_189_ = lean_nat_abs(v_x_184_);
        v___x_190_ = leanh::lean_apply_1(v_h__1_185_, v_a_189_);
        return v___x_190_;
    } else {
        let mut v_abs_191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_185_);
        v_abs_191_ = lean_nat_abs(v_x_184_);
        v_one_192_ = leanh::lean_unsigned_to_nat(1);
        v_a_193_ = lean_nat_sub(v_abs_191_, v_one_192_);
        leanh::lean_dec(v_abs_191_);
        v___x_194_ = leanh::lean_apply_1(v_h__2_186_, v_a_193_);
        return v___x_194_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(
    mut v_motive_195_: *mut leanh::LeanObject,
    mut v_x_196_: *mut leanh::LeanObject,
    mut v_h__1_197_: *mut leanh::LeanObject,
    mut v_h__2_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(
        v_motive_195_,
        v_x_196_,
        v_h__1_197_,
        v_h__2_198_,
    );
    leanh::lean_dec(v_x_196_);
    return v_res_199_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(
    mut v_x_200_: u8,
    mut v_x_201_: u8,
    mut v_h__1_202_: *mut leanh::LeanObject,
    mut v_h__2_203_: *mut leanh::LeanObject,
    mut v_h__3_204_: *mut leanh::LeanObject,
    mut v_h__4_205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_200_ == 0 {
        leanh::lean_dec(v_h__4_205_);
        leanh::lean_dec(v_h__3_204_);
        if v_x_201_ == 0 {
            let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_203_);
            v___x_206_ = leanh::lean_box(0);
            v___x_207_ = leanh::lean_apply_1(v_h__1_202_, v___x_206_);
            return v___x_207_;
        } else {
            let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_202_);
            v___x_208_ = leanh::lean_box(0);
            v___x_209_ = leanh::lean_apply_1(v_h__2_203_, v___x_208_);
            return v___x_209_;
        }
    } else {
        leanh::lean_dec(v_h__2_203_);
        leanh::lean_dec(v_h__1_202_);
        if v_x_201_ == 0 {
            let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_205_);
            v___x_210_ = leanh::lean_box(0);
            v___x_211_ = leanh::lean_apply_1(v_h__3_204_, v___x_210_);
            return v___x_211_;
        } else {
            let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_204_);
            v___x_212_ = leanh::lean_box(0);
            v___x_213_ = leanh::lean_apply_1(v_h__4_205_, v___x_212_);
            return v___x_213_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(
    mut v_x_214_: *mut leanh::LeanObject,
    mut v_x_215_: *mut leanh::LeanObject,
    mut v_h__1_216_: *mut leanh::LeanObject,
    mut v_h__2_217_: *mut leanh::LeanObject,
    mut v_h__3_218_: *mut leanh::LeanObject,
    mut v_h__4_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_50__boxed_220_: u8 = 0;
    let mut v_x_51__boxed_221_: u8 = 0;
    let mut v_res_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_50__boxed_220_ = (leanh::lean_unbox(v_x_214_) as u8);
    v_x_51__boxed_221_ = (leanh::lean_unbox(v_x_215_) as u8);
    v_res_222_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(
        v_x_50__boxed_220_,
        v_x_51__boxed_221_,
        v_h__1_216_,
        v_h__2_217_,
        v_h__3_218_,
        v_h__4_219_,
    );
    return v_res_222_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(
    mut v_motive_223_: *mut leanh::LeanObject,
    mut v_x_224_: u8,
    mut v_x_225_: u8,
    mut v_h__1_226_: *mut leanh::LeanObject,
    mut v_h__2_227_: *mut leanh::LeanObject,
    mut v_h__3_228_: *mut leanh::LeanObject,
    mut v_h__4_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_224_ == 0 {
        leanh::lean_dec(v_h__4_229_);
        leanh::lean_dec(v_h__3_228_);
        if v_x_225_ == 0 {
            let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_227_);
            v___x_230_ = leanh::lean_box(0);
            v___x_231_ = leanh::lean_apply_1(v_h__1_226_, v___x_230_);
            return v___x_231_;
        } else {
            let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_226_);
            v___x_232_ = leanh::lean_box(0);
            v___x_233_ = leanh::lean_apply_1(v_h__2_227_, v___x_232_);
            return v___x_233_;
        }
    } else {
        leanh::lean_dec(v_h__2_227_);
        leanh::lean_dec(v_h__1_226_);
        if v_x_225_ == 0 {
            let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_229_);
            v___x_234_ = leanh::lean_box(0);
            v___x_235_ = leanh::lean_apply_1(v_h__3_228_, v___x_234_);
            return v___x_235_;
        } else {
            let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_228_);
            v___x_236_ = leanh::lean_box(0);
            v___x_237_ = leanh::lean_apply_1(v_h__4_229_, v___x_236_);
            return v___x_237_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(
    mut v_motive_238_: *mut leanh::LeanObject,
    mut v_x_239_: *mut leanh::LeanObject,
    mut v_x_240_: *mut leanh::LeanObject,
    mut v_h__1_241_: *mut leanh::LeanObject,
    mut v_h__2_242_: *mut leanh::LeanObject,
    mut v_h__3_243_: *mut leanh::LeanObject,
    mut v_h__4_244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_72__boxed_245_: u8 = 0;
    let mut v_x_73__boxed_246_: u8 = 0;
    let mut v_res_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_72__boxed_245_ = (leanh::lean_unbox(v_x_239_) as u8);
    v_x_73__boxed_246_ = (leanh::lean_unbox(v_x_240_) as u8);
    v_res_247_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(
        v_motive_238_,
        v_x_72__boxed_245_,
        v_x_73__boxed_246_,
        v_h__1_241_,
        v_h__2_242_,
        v_h__3_243_,
        v_h__4_244_,
    );
    return v_res_247_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(
    mut v_x_248_: *mut leanh::LeanObject,
    mut v_h__1_249_: *mut leanh::LeanObject,
    mut v_h__2_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_248_) == 0 {
        let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_250_);
        v___x_251_ = leanh::lean_box(0);
        v___x_252_ = leanh::lean_apply_1(v_h__1_249_, v___x_251_);
        return v___x_252_;
    } else {
        let mut v_head_253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_249_);
        v_head_253_ = leanh::lean_ctor_get(v_x_248_, 0);
        leanh::lean_inc(v_head_253_);
        v_tail_254_ = leanh::lean_ctor_get(v_x_248_, 1);
        leanh::lean_inc(v_tail_254_);
        leanh::lean_dec_ref_known(v_x_248_, 2);
        v___x_255_ = leanh::lean_apply_2(v_h__2_250_, v_head_253_, v_tail_254_);
        return v___x_255_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(
    mut v_motive_256_: *mut leanh::LeanObject,
    mut v_x_257_: *mut leanh::LeanObject,
    mut v_h__1_258_: *mut leanh::LeanObject,
    mut v_h__2_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_259_);
        v___x_260_ = leanh::lean_box(0);
        v___x_261_ = leanh::lean_apply_1(v_h__1_258_, v___x_260_);
        return v___x_261_;
    } else {
        let mut v_head_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_258_);
        v_head_262_ = leanh::lean_ctor_get(v_x_257_, 0);
        leanh::lean_inc(v_head_262_);
        v_tail_263_ = leanh::lean_ctor_get(v_x_257_, 1);
        leanh::lean_inc(v_tail_263_);
        leanh::lean_dec_ref_known(v_x_257_, 2);
        v___x_264_ = leanh::lean_apply_2(v_h__2_259_, v_head_262_, v_tail_263_);
        return v___x_264_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(
    mut v_x_265_: *mut leanh::LeanObject,
    mut v_x_266_: *mut leanh::LeanObject,
    mut v_h__1_267_: *mut leanh::LeanObject,
    mut v_h__2_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_270_: u8 = 0;
    v_zero_269_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_270_ = lean_nat_dec_eq(v_x_265_, v_zero_269_);
    if v_isZero_270_ == 1 {
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_268_);
        v___x_271_ = leanh::lean_apply_1(v_h__1_267_, v_x_266_);
        return v___x_271_;
    } else {
        let mut v_one_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_267_);
        v_one_272_ = leanh::lean_unsigned_to_nat(1);
        v_n_273_ = lean_nat_sub(v_x_265_, v_one_272_);
        v___x_274_ = leanh::lean_apply_2(v_h__2_268_, v_n_273_, v_x_266_);
        return v___x_274_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(
    mut v_x_275_: *mut leanh::LeanObject,
    mut v_x_276_: *mut leanh::LeanObject,
    mut v_h__1_277_: *mut leanh::LeanObject,
    mut v_h__2_278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_279_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(
        v_x_275_,
        v_x_276_,
        v_h__1_277_,
        v_h__2_278_,
    );
    leanh::lean_dec(v_x_275_);
    return v_res_279_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(
    mut v_w_280_: *mut leanh::LeanObject,
    mut v_motive_281_: *mut leanh::LeanObject,
    mut v_x_282_: *mut leanh::LeanObject,
    mut v_x_283_: *mut leanh::LeanObject,
    mut v_h__1_284_: *mut leanh::LeanObject,
    mut v_h__2_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_287_: u8 = 0;
    v_zero_286_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_287_ = lean_nat_dec_eq(v_x_282_, v_zero_286_);
    if v_isZero_287_ == 1 {
        let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_285_);
        v___x_288_ = leanh::lean_apply_1(v_h__1_284_, v_x_283_);
        return v___x_288_;
    } else {
        let mut v_one_289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_290_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_284_);
        v_one_289_ = leanh::lean_unsigned_to_nat(1);
        v_n_290_ = lean_nat_sub(v_x_282_, v_one_289_);
        v___x_291_ = leanh::lean_apply_2(v_h__2_285_, v_n_290_, v_x_283_);
        return v___x_291_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(
    mut v_w_292_: *mut leanh::LeanObject,
    mut v_motive_293_: *mut leanh::LeanObject,
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_x_295_: *mut leanh::LeanObject,
    mut v_h__1_296_: *mut leanh::LeanObject,
    mut v_h__2_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(
        v_w_292_,
        v_motive_293_,
        v_x_294_,
        v_x_295_,
        v_h__1_296_,
        v_h__2_297_,
    );
    leanh::lean_dec(v_x_294_);
    leanh::lean_dec(v_w_292_);
    return v_res_298_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(
    mut v_x_299_: *mut leanh::LeanObject,
    mut v_x_300_: *mut leanh::LeanObject,
    mut v_h__1_301_: *mut leanh::LeanObject,
    mut v_h__2_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_304_: u8 = 0;
    v_zero_303_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_304_ = lean_nat_dec_eq(v_x_299_, v_zero_303_);
    if v_isZero_304_ == 1 {
        let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_302_);
        v___x_305_ = leanh::lean_apply_1(v_h__1_301_, v_x_300_);
        return v___x_305_;
    } else {
        let mut v_one_306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_301_);
        v_one_306_ = leanh::lean_unsigned_to_nat(1);
        v_n_307_ = lean_nat_sub(v_x_299_, v_one_306_);
        v___x_308_ = leanh::lean_apply_2(v_h__2_302_, v_n_307_, v_x_300_);
        return v___x_308_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(
    mut v_x_309_: *mut leanh::LeanObject,
    mut v_x_310_: *mut leanh::LeanObject,
    mut v_h__1_311_: *mut leanh::LeanObject,
    mut v_h__2_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(
        v_x_309_,
        v_x_310_,
        v_h__1_311_,
        v_h__2_312_,
    );
    leanh::lean_dec(v_x_309_);
    return v_res_313_;
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(
    mut v_motive_314_: *mut leanh::LeanObject,
    mut v_x_315_: *mut leanh::LeanObject,
    mut v_x_316_: *mut leanh::LeanObject,
    mut v_h__1_317_: *mut leanh::LeanObject,
    mut v_h__2_318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_320_: u8 = 0;
    v_zero_319_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_320_ = lean_nat_dec_eq(v_x_315_, v_zero_319_);
    if v_isZero_320_ == 1 {
        let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_318_);
        v___x_321_ = leanh::lean_apply_1(v_h__1_317_, v_x_316_);
        return v___x_321_;
    } else {
        let mut v_one_322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_323_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_317_);
        v_one_322_ = leanh::lean_unsigned_to_nat(1);
        v_n_323_ = lean_nat_sub(v_x_315_, v_one_322_);
        v___x_324_ = leanh::lean_apply_2(v_h__2_318_, v_n_323_, v_x_316_);
        return v___x_324_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(
    mut v_motive_325_: *mut leanh::LeanObject,
    mut v_x_326_: *mut leanh::LeanObject,
    mut v_x_327_: *mut leanh::LeanObject,
    mut v_h__1_328_: *mut leanh::LeanObject,
    mut v_h__2_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(
        v_motive_325_,
        v_x_326_,
        v_x_327_,
        v_h__1_328_,
        v_h__2_329_,
    );
    leanh::lean_dec(v_x_326_);
    return v_res_330_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Mod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_Lemmas(
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
pub unsafe fn initialize_Init_Data_BitVec_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Mod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_BitVec_Lemmas(builtin);
}