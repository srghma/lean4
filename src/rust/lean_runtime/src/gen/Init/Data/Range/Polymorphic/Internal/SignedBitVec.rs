// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Internal.SignedBitVec
// Imports: Init.Data.BitVec.Bootstrap Init.Data.BitVec.Lemmas Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.Data.Nat.Div.Lemmas Init.Data.Nat.Lemmas Init.Data.Nat.Mod Init.Data.Option.Lemmas Init.Data.Range.Polymorphic.BitVec Init.Omega
use crate::r#gen::Init::Data::BitVec::Basic::{l_BitVec_sle, l_BitVec_slt};
use crate::r#gen::Init::Data::BitVec::BasicAux::l_BitVec_add;
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Div::Lemmas::{
    initialize_Init_Data_Nat_Div_Lemmas, runtime_initialize_Init_Data_Nat_Div_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Mod::{
    initialize_Init_Data_Nat_Mod, runtime_initialize_Init_Data_Nat_Mod,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Range::Polymorphic::BitVec::{
    initialize_Init_Data_Range_Polymorphic_BitVec,
    runtime_initialize_Init_Data_Range_Polymorphic_BitVec,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_pow, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0(
    mut v_n_131_: *mut LeanObject,
    mut v_a_132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    v___x_133_ = l_BitVec_ofNat(v_n_131_, v_a_132_);
    return v___x_133_;
}
pub unsafe fn l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0___boxed(
    mut v_n_134_: *mut LeanObject,
    mut v_a_135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_136_: *mut LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Nat_cast___at___00__private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed_spec__0(v_n_134_, v_a_135_);
    lean_dec(v_a_135_);
    lean_dec(v_n_134_);
    return v_res_136_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(
    mut v_n_137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    v___x_138_ = lean_unsigned_to_nat(2);
    v___x_139_ = lean_unsigned_to_nat(1);
    v___x_140_ = lean_nat_sub(v_n_137_, v___x_139_);
    v___x_141_ = lean_nat_pow(v___x_138_, v___x_140_);
    lean_dec(v___x_140_);
    v___x_142_ = l_BitVec_ofNat(v_n_137_, v___x_141_);
    lean_dec(v___x_141_);
    return v___x_142_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed___boxed(
    mut v_n_143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_144_: *mut LeanObject = core::ptr::null_mut();
    v_res_144_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(
            v_n_143_,
        );
    lean_dec(v_n_143_);
    return v_res_144_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed(
    mut v_n_145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    v___x_146_ = lean_unsigned_to_nat(2);
    v___x_147_ = lean_unsigned_to_nat(1);
    v___x_148_ = lean_nat_sub(v_n_145_, v___x_147_);
    v___x_149_ = lean_nat_pow(v___x_146_, v___x_148_);
    lean_dec(v___x_148_);
    v___x_150_ = lean_nat_sub(v___x_149_, v___x_147_);
    lean_dec(v___x_149_);
    v___x_151_ = l_BitVec_ofNat(v_n_145_, v___x_150_);
    lean_dec(v___x_150_);
    return v___x_151_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed___boxed(
    mut v_n_152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_153_: *mut LeanObject = core::ptr::null_mut();
    v_res_153_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMaxSealed(
            v_n_152_,
        );
    lean_dec(v_n_152_);
    return v_res_153_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
    mut v_n_154_: *mut LeanObject,
    mut v_x_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v___x_156_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_intMinSealed(
            v_n_154_,
        );
    v___x_157_ = l_BitVec_add(v_n_154_, v_x_155_, v___x_156_);
    lean_dec(v___x_156_);
    return v___x_157_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate___boxed(
    mut v_n_158_: *mut LeanObject,
    mut v_x_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_160_: *mut LeanObject = core::ptr::null_mut();
    v_res_160_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_158_, v_x_159_,
        );
    lean_dec(v_x_159_);
    lean_dec(v_n_158_);
    return v_res_160_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0(
    mut v_n_161_: *mut LeanObject,
    mut v_x_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: u8 = 0;
    v___x_163_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_161_, v_x_162_,
        );
    v___x_164_ = lean_unsigned_to_nat(1);
    v___x_165_ = l_BitVec_ofNat(v_n_161_, v___x_164_);
    v___x_166_ = l_BitVec_add(v_n_161_, v___x_163_, v___x_165_);
    lean_dec(v___x_165_);
    lean_dec(v___x_163_);
    v___x_167_ = lean_unsigned_to_nat(0);
    v___x_168_ = l_BitVec_ofNat(v_n_161_, v___x_167_);
    v___x_169_ = lean_nat_dec_eq(v___x_166_, v___x_168_);
    lean_dec(v___x_168_);
    if v___x_169_ == 0 {
        let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
        v___x_170_ =
            l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
                v_n_161_, v___x_166_,
            );
        lean_dec(v___x_166_);
        v___x_171_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_171_, 0, v___x_170_);
        return v___x_171_;
    } else {
        let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_166_);
        v___x_172_ = lean_box(0);
        return v___x_172_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0___boxed(
    mut v_n_173_: *mut LeanObject,
    mut v_x_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_175_: *mut LeanObject = core::ptr::null_mut();
    v_res_175_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0(v_n_173_, v_x_174_);
    lean_dec(v_x_174_);
    lean_dec(v_n_173_);
    return v_res_175_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1(
    mut v_n_176_: *mut LeanObject,
    mut v_n_177_: *mut LeanObject,
    mut v_x_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: u8 = 0;
    v___x_179_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_176_, v_x_178_,
        );
    v___x_180_ = lean_nat_add(v___x_179_, v_n_177_);
    lean_dec(v___x_179_);
    v___x_181_ = lean_unsigned_to_nat(2);
    v___x_182_ = lean_nat_pow(v___x_181_, v_n_176_);
    v___x_183_ = lean_nat_dec_lt(v___x_180_, v___x_182_);
    lean_dec(v___x_182_);
    if v___x_183_ == 0 {
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_180_);
        v___x_184_ = lean_box(0);
        return v___x_184_;
    } else {
        let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        v___x_185_ =
            l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
                v_n_176_, v___x_180_,
            );
        lean_dec(v___x_180_);
        v___x_186_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_186_, 0, v___x_185_);
        return v___x_186_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1___boxed(
    mut v_n_187_: *mut LeanObject,
    mut v_n_188_: *mut LeanObject,
    mut v_x_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_190_: *mut LeanObject = core::ptr::null_mut();
    v_res_190_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1(v_n_187_, v_n_188_, v_x_189_);
    lean_dec(v_x_189_);
    lean_dec(v_n_188_);
    lean_dec(v_n_187_);
    return v_res_190_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable(
    mut v_n_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_191_);
    v___f_192_ = lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_192_, 0, v_n_191_);
    v___f_193_ = lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instUpwardEnumerable___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_193_, 0, v_n_191_);
    v___x_194_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_194_, 0, v___f_192_);
    lean_ctor_set(v___x_194_, 1, v___f_193_);
    return v___x_194_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE(
    mut v_n_195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    v___x_196_ = lean_box(0);
    return v___x_196_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE___boxed(
    mut v_n_197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_198_: *mut LeanObject = core::ptr::null_mut();
    v_res_198_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLE(
            v_n_197_,
        );
    lean_dec(v_n_197_);
    return v_res_198_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT(
    mut v_n_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    v___x_200_ = lean_box(0);
    return v___x_200_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT___boxed(
    mut v_n_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_202_: *mut LeanObject = core::ptr::null_mut();
    v_res_202_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instLT(
            v_n_201_,
        );
    lean_dec(v_n_201_);
    return v_res_202_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE(
    mut v_n_203_: *mut LeanObject,
    mut v_x_204_: *mut LeanObject,
    mut v_y_205_: *mut LeanObject,
) -> u8 {
    let mut v___x_206_: u8 = 0;
    v___x_206_ = l_BitVec_sle(v_n_203_, v_x_204_, v_y_205_);
    return v___x_206_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE___boxed(
    mut v_n_207_: *mut LeanObject,
    mut v_x_208_: *mut LeanObject,
    mut v_y_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_210_: u8 = 0;
    let mut v_r_211_: *mut LeanObject = core::ptr::null_mut();
    v_res_210_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLE(v_n_207_, v_x_208_, v_y_209_);
    lean_dec(v_n_207_);
    v_r_211_ = lean_box((v_res_210_) as usize);
    return v_r_211_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT(
    mut v_n_212_: *mut LeanObject,
    mut v_x_213_: *mut LeanObject,
    mut v_y_214_: *mut LeanObject,
) -> u8 {
    let mut v___x_215_: u8 = 0;
    v___x_215_ = l_BitVec_slt(v_n_212_, v_x_213_, v_y_214_);
    return v___x_215_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT___boxed(
    mut v_n_216_: *mut LeanObject,
    mut v_x_217_: *mut LeanObject,
    mut v_y_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_219_: u8 = 0;
    let mut v_r_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_219_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instDecidableLT(v_n_216_, v_x_217_, v_y_218_);
    lean_dec(v_n_216_);
    v_r_220_ = lean_box((v_res_219_) as usize);
    return v_r_220_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0(
    mut v_n_221_: *mut LeanObject,
    mut v_lo_222_: *mut LeanObject,
    mut v_hi_223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_224_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_221_, v_lo_222_,
        );
    v___x_225_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_221_, v_hi_223_,
        );
    v___x_226_ = lean_unsigned_to_nat(1);
    v___x_227_ = lean_nat_add(v___x_225_, v___x_226_);
    lean_dec(v___x_225_);
    v___x_228_ = lean_nat_sub(v___x_227_, v___x_224_);
    lean_dec(v___x_224_);
    lean_dec(v___x_227_);
    return v___x_228_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0___boxed(
    mut v_n_229_: *mut LeanObject,
    mut v_lo_230_: *mut LeanObject,
    mut v_hi_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_232_: *mut LeanObject = core::ptr::null_mut();
    v_res_232_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0(v_n_229_, v_lo_230_, v_hi_231_);
    lean_dec(v_hi_231_);
    lean_dec(v_lo_230_);
    lean_dec(v_n_229_);
    return v_res_232_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize(
    mut v_n_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_234_: *mut LeanObject = core::ptr::null_mut();
    v___f_234_ = lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxcHasSize___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_234_, 0, v_n_233_);
    return v___f_234_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0(
    mut v_n_235_: *mut LeanObject,
    mut v_lo_236_: *mut LeanObject,
    mut v_hi_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    v___x_238_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_235_, v_lo_236_,
        );
    v___x_239_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_235_, v_hi_237_,
        );
    v___x_240_ = lean_unsigned_to_nat(1);
    v___x_241_ = lean_nat_add(v___x_239_, v___x_240_);
    lean_dec(v___x_239_);
    v___x_242_ = lean_nat_sub(v___x_241_, v___x_238_);
    lean_dec(v___x_238_);
    lean_dec(v___x_241_);
    v___x_243_ = lean_nat_sub(v___x_242_, v___x_240_);
    lean_dec(v___x_242_);
    return v___x_243_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0___boxed(
    mut v_n_244_: *mut LeanObject,
    mut v_lo_245_: *mut LeanObject,
    mut v_hi_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_247_: *mut LeanObject = core::ptr::null_mut();
    v_res_247_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0(v_n_244_, v_lo_245_, v_hi_246_);
    lean_dec(v_hi_246_);
    lean_dec(v_lo_245_);
    lean_dec(v_n_244_);
    return v_res_247_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize(
    mut v_n_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_249_: *mut LeanObject = core::ptr::null_mut();
    v___f_249_ = lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxoHasSize___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_249_, 0, v_n_248_);
    return v___f_249_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0(
    mut v_n_250_: *mut LeanObject,
    mut v_lo_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = lean_unsigned_to_nat(2);
    v___x_253_ = lean_nat_pow(v___x_252_, v_n_250_);
    v___x_254_ =
        l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_rotate(
            v_n_250_, v_lo_251_,
        );
    v___x_255_ = lean_nat_sub(v___x_253_, v___x_254_);
    lean_dec(v___x_254_);
    lean_dec(v___x_253_);
    return v___x_255_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0___boxed(
    mut v_n_256_: *mut LeanObject,
    mut v_lo_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_258_: *mut LeanObject = core::ptr::null_mut();
    v_res_258_ = l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0(v_n_256_, v_lo_257_);
    lean_dec(v_lo_257_);
    lean_dec(v_n_256_);
    return v_res_258_;
}
pub unsafe fn l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize(
    mut v_n_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_260_: *mut LeanObject = core::ptr::null_mut();
    v___f_260_ = lean_alloc_closure(l___private_Init_Data_Range_Polymorphic_Internal_SignedBitVec_0__BitVec_Signed_instRxiHasSize___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_260_, 0, v_n_259_);
    return v___f_260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Mod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Mod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
}
