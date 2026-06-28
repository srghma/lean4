// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename
// Imports: Init.Data.Int.Linear Lean.Meta.Tactic.Grind.VarRename
use crate::r#gen::Init::Data::Int::Linear::{
    initialize_Init_Data_Int_Linear, runtime_initialize_Init_Data_Int_Linear,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_VarRename, l_Lean_Meta_Grind_collectVar,
    runtime_initialize_Lean_Meta_Tactic_Grind_VarRename,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_size, lean_nat_dec_eq};
pub static l_Int_Linear_Expr_renameVars___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Int_Linear_Expr_renameVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Expr_renameVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0___redArg(
    mut v_a_164_: *mut crate::leanh::LeanObject,
    mut v_x_165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: u8 = 0;
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_165_) == 0 {
                    v___x_166_ = crate::leanh::lean_box(0);
                    return v___x_166_;
                } else {
                    v_key_167_ = crate::leanh::lean_ctor_get(v_x_165_, 0);
                    v_value_168_ = crate::leanh::lean_ctor_get(v_x_165_, 1);
                    v_tail_169_ = crate::leanh::lean_ctor_get(v_x_165_, 2);
                    v___x_170_ = lean_nat_dec_eq(v_key_167_, v_a_164_);
                    if v___x_170_ == 0 {
                        v_x_165_ = v_tail_169_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_168_);
                        v___x_172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_172_, 0, v_value_168_);
                        return v___x_172_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0___redArg___boxed(
    mut v_a_173_: *mut crate::leanh::LeanObject,
    mut v_x_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_175_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0___redArg(v_a_173_, v_x_174_);
    crate::leanh::lean_dec(v_x_174_);
    crate::leanh::lean_dec(v_a_173_);
    return v_res_175_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___redArg(
    mut v_m_176_: *mut crate::leanh::LeanObject,
    mut v_a_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: u64 = 0;
    let mut v___x_181_: u64 = 0;
    let mut v___x_182_: u64 = 0;
    let mut v_fold_183_: u64 = 0;
    let mut v___x_184_: u64 = 0;
    let mut v___x_185_: u64 = 0;
    let mut v___x_186_: u64 = 0;
    let mut v___x_187_: usize = 0;
    let mut v___x_188_: usize = 0;
    let mut v___x_189_: usize = 0;
    let mut v___x_190_: usize = 0;
    let mut v___x_191_: usize = 0;
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_178_ = crate::leanh::lean_ctor_get(v_m_176_, 1);
    v___x_179_ = lean_array_get_size(v_buckets_178_);
    v___x_180_ = lean_uint64_of_nat(v_a_177_);
    v___x_181_ = 32u64;
    v___x_182_ = lean_uint64_shift_right(v___x_180_, v___x_181_);
    v_fold_183_ = lean_uint64_xor(v___x_180_, v___x_182_);
    v___x_184_ = 16u64;
    v___x_185_ = lean_uint64_shift_right(v_fold_183_, v___x_184_);
    v___x_186_ = lean_uint64_xor(v_fold_183_, v___x_185_);
    v___x_187_ = lean_uint64_to_usize(v___x_186_);
    v___x_188_ = lean_usize_of_nat(v___x_179_);
    v___x_189_ = 1usize;
    v___x_190_ = lean_usize_sub(v___x_188_, v___x_189_);
    v___x_191_ = lean_usize_land(v___x_187_, v___x_190_);
    v___x_192_ = lean_array_uget_borrowed(v_buckets_178_, v___x_191_);
    v___x_193_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0___redArg(v_a_177_, v___x_192_);
    return v___x_193_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___redArg___boxed(
    mut v_m_194_: *mut crate::leanh::LeanObject,
    mut v_a_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___redArg(v_m_194_, v_a_195_);
    crate::leanh::lean_dec(v_a_195_);
    crate::leanh::lean_dec_ref(v_m_194_);
    return v_res_196_;
}
pub unsafe fn l_Int_Linear_Poly_renameVars(
    mut v_p_197_: *mut crate::leanh::LeanObject,
    mut v_f_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_204_: u8 = 0;
    let mut v___y_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_197_) == 0 {
                    return v_p_197_;
                } else {
                    v_k_199_ = crate::leanh::lean_ctor_get(v_p_197_, 0);
                    v_v_200_ = crate::leanh::lean_ctor_get(v_p_197_, 1);
                    v_p_201_ = crate::leanh::lean_ctor_get(v_p_197_, 2);
                    v_isSharedCheck_214_ = (!crate::leanh::lean_is_exclusive(v_p_197_)) as u8;
                    if v_isSharedCheck_214_ == 0 {
                        v___x_203_ = v_p_197_;
                        v_isShared_204_ = v_isSharedCheck_214_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_201_);
                        crate::leanh::lean_inc(v_v_200_);
                        crate::leanh::lean_inc(v_k_199_);
                        crate::leanh::lean_dec(v_p_197_);
                        v___x_203_ = crate::leanh::lean_box(0);
                        v_isShared_204_ = v_isSharedCheck_214_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___redArg(v_f_198_, v_v_200_);
                crate::leanh::lean_dec(v_v_200_);
                if crate::leanh::lean_obj_tag(v___x_211_) == 0 {
                    v___x_212_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_206_ = v___x_212_;
                    state = 2;
                    continue;
                } else {
                    v_val_213_ = crate::leanh::lean_ctor_get(v___x_211_, 0);
                    crate::leanh::lean_inc(v_val_213_);
                    crate::leanh::lean_dec_ref_known(v___x_211_, 1);
                    v___y_206_ = v_val_213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_207_ = l_Int_Linear_Poly_renameVars(v_p_201_, v_f_198_);
                if v_isShared_204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_203_, 2, v___x_207_);
                    crate::leanh::lean_ctor_set(v___x_203_, 1, v___y_206_);
                    v___x_209_ = v___x_203_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_210_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_210_, 0, v_k_199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_210_, 1, v___y_206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_210_, 2, v___x_207_);
                    v___x_209_ = v_reuseFailAlloc_210_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_renameVars___boxed(
    mut v_p_215_: *mut crate::leanh::LeanObject,
    mut v_f_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_217_ = l_Int_Linear_Poly_renameVars(v_p_215_, v_f_216_);
    crate::leanh::lean_dec_ref(v_f_216_);
    return v_res_217_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0(
    mut v_00_u03b2_218_: *mut crate::leanh::LeanObject,
    mut v_m_219_: *mut crate::leanh::LeanObject,
    mut v_a_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___redArg(v_m_219_, v_a_220_);
    return v___x_221_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___boxed(
    mut v_00_u03b2_222_: *mut crate::leanh::LeanObject,
    mut v_m_223_: *mut crate::leanh::LeanObject,
    mut v_a_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_225_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0(
            v_00_u03b2_222_,
            v_m_223_,
            v_a_224_,
        );
    crate::leanh::lean_dec(v_a_224_);
    crate::leanh::lean_dec_ref(v_m_223_);
    return v_res_225_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0(
    mut v_00_u03b2_226_: *mut crate::leanh::LeanObject,
    mut v_a_227_: *mut crate::leanh::LeanObject,
    mut v_x_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0___redArg(v_a_227_, v_x_228_);
    return v___x_229_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0___boxed(
    mut v_00_u03b2_230_: *mut crate::leanh::LeanObject,
    mut v_a_231_: *mut crate::leanh::LeanObject,
    mut v_x_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0_spec__0(v_00_u03b2_230_, v_a_231_, v_x_232_);
    crate::leanh::lean_dec(v_x_232_);
    crate::leanh::lean_dec(v_a_231_);
    return v_res_233_;
}
pub unsafe fn l_Int_Linear_Expr_renameVars(
    mut v_e_236_: *mut crate::leanh::LeanObject,
    mut v_f_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_241_: u8 = 0;
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_248_: u8 = 0;
    let mut v_a_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_253_: u8 = 0;
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_259_: u8 = 0;
    let mut v_a_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_264_: u8 = 0;
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_270_: u8 = 0;
    let mut v_a_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_274_: u8 = 0;
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_279_: u8 = 0;
    let mut v_k_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_284_: u8 = 0;
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_289_: u8 = 0;
    let mut v_a_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_294_: u8 = 0;
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_236_) {
                0 => {
                    return v_e_236_;
                }
                1 => {
                    v_i_238_ = crate::leanh::lean_ctor_get(v_e_236_, 0);
                    v_isSharedCheck_248_ = (!crate::leanh::lean_is_exclusive(v_e_236_)) as u8;
                    if v_isSharedCheck_248_ == 0 {
                        v___x_240_ = v_e_236_;
                        v_isShared_241_ = v_isSharedCheck_248_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_i_238_);
                        crate::leanh::lean_dec(v_e_236_);
                        v___x_240_ = crate::leanh::lean_box(0);
                        v_isShared_241_ = v_isSharedCheck_248_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_a_249_ = crate::leanh::lean_ctor_get(v_e_236_, 0);
                    v_b_250_ = crate::leanh::lean_ctor_get(v_e_236_, 1);
                    v_isSharedCheck_259_ = (!crate::leanh::lean_is_exclusive(v_e_236_)) as u8;
                    if v_isSharedCheck_259_ == 0 {
                        v___x_252_ = v_e_236_;
                        v_isShared_253_ = v_isSharedCheck_259_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_250_);
                        crate::leanh::lean_inc(v_a_249_);
                        crate::leanh::lean_dec(v_e_236_);
                        v___x_252_ = crate::leanh::lean_box(0);
                        v_isShared_253_ = v_isSharedCheck_259_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_a_260_ = crate::leanh::lean_ctor_get(v_e_236_, 0);
                    v_b_261_ = crate::leanh::lean_ctor_get(v_e_236_, 1);
                    v_isSharedCheck_270_ = (!crate::leanh::lean_is_exclusive(v_e_236_)) as u8;
                    if v_isSharedCheck_270_ == 0 {
                        v___x_263_ = v_e_236_;
                        v_isShared_264_ = v_isSharedCheck_270_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_261_);
                        crate::leanh::lean_inc(v_a_260_);
                        crate::leanh::lean_dec(v_e_236_);
                        v___x_263_ = crate::leanh::lean_box(0);
                        v_isShared_264_ = v_isSharedCheck_270_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_a_271_ = crate::leanh::lean_ctor_get(v_e_236_, 0);
                    v_isSharedCheck_279_ = (!crate::leanh::lean_is_exclusive(v_e_236_)) as u8;
                    if v_isSharedCheck_279_ == 0 {
                        v___x_273_ = v_e_236_;
                        v_isShared_274_ = v_isSharedCheck_279_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_271_);
                        crate::leanh::lean_dec(v_e_236_);
                        v___x_273_ = crate::leanh::lean_box(0);
                        v_isShared_274_ = v_isSharedCheck_279_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v_k_280_ = crate::leanh::lean_ctor_get(v_e_236_, 0);
                    v_a_281_ = crate::leanh::lean_ctor_get(v_e_236_, 1);
                    v_isSharedCheck_289_ = (!crate::leanh::lean_is_exclusive(v_e_236_)) as u8;
                    if v_isSharedCheck_289_ == 0 {
                        v___x_283_ = v_e_236_;
                        v_isShared_284_ = v_isSharedCheck_289_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_281_);
                        crate::leanh::lean_inc(v_k_280_);
                        crate::leanh::lean_dec(v_e_236_);
                        v___x_283_ = crate::leanh::lean_box(0);
                        v_isShared_284_ = v_isSharedCheck_289_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    v_a_290_ = crate::leanh::lean_ctor_get(v_e_236_, 0);
                    v_k_291_ = crate::leanh::lean_ctor_get(v_e_236_, 1);
                    v_isSharedCheck_299_ = (!crate::leanh::lean_is_exclusive(v_e_236_)) as u8;
                    if v_isSharedCheck_299_ == 0 {
                        v___x_293_ = v_e_236_;
                        v_isShared_294_ = v_isSharedCheck_299_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_291_);
                        crate::leanh::lean_inc(v_a_290_);
                        crate::leanh::lean_dec(v_e_236_);
                        v___x_293_ = crate::leanh::lean_box(0);
                        v_isShared_294_ = v_isSharedCheck_299_;
                        state = 11;
                        continue;
                    }
                }
            },
            1 => {
                v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Int_Linear_Poly_renameVars_spec__0___redArg(v_f_237_, v_i_238_);
                crate::leanh::lean_dec(v_i_238_);
                if crate::leanh::lean_obj_tag(v___x_242_) == 0 {
                    crate::leanh::lean_del_object(v___x_240_);
                    v___x_243_ = l_Int_Linear_Expr_renameVars___closed__0;
                    return v___x_243_;
                } else {
                    v_val_244_ = crate::leanh::lean_ctor_get(v___x_242_, 0);
                    crate::leanh::lean_inc(v_val_244_);
                    crate::leanh::lean_dec_ref_known(v___x_242_, 1);
                    if v_isShared_241_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_240_, 0, v_val_244_);
                        v___x_246_ = v___x_240_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_247_, 0, v_val_244_);
                        v___x_246_ = v_reuseFailAlloc_247_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_246_;
            }
            3 => {
                v___x_254_ = l_Int_Linear_Expr_renameVars(v_a_249_, v_f_237_);
                v___x_255_ = l_Int_Linear_Expr_renameVars(v_b_250_, v_f_237_);
                if v_isShared_253_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_252_, 1, v___x_255_);
                    crate::leanh::lean_ctor_set(v___x_252_, 0, v___x_254_);
                    v___x_257_ = v___x_252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_258_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_255_);
                    v___x_257_ = v_reuseFailAlloc_258_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_257_;
            }
            5 => {
                v___x_265_ = l_Int_Linear_Expr_renameVars(v_a_260_, v_f_237_);
                v___x_266_ = l_Int_Linear_Expr_renameVars(v_b_261_, v_f_237_);
                if v_isShared_264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_263_, 1, v___x_266_);
                    crate::leanh::lean_ctor_set(v___x_263_, 0, v___x_265_);
                    v___x_268_ = v___x_263_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_269_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_266_);
                    v___x_268_ = v_reuseFailAlloc_269_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_268_;
            }
            7 => {
                v___x_275_ = l_Int_Linear_Expr_renameVars(v_a_271_, v_f_237_);
                if v_isShared_274_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_273_, 0, v___x_275_);
                    v___x_277_ = v___x_273_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_278_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
                    v___x_277_ = v_reuseFailAlloc_278_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_277_;
            }
            9 => {
                v___x_285_ = l_Int_Linear_Expr_renameVars(v_a_281_, v_f_237_);
                if v_isShared_284_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_283_, 1, v___x_285_);
                    v___x_287_ = v___x_283_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_288_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_288_, 0, v_k_280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_285_);
                    v___x_287_ = v_reuseFailAlloc_288_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_287_;
            }
            11 => {
                v___x_295_ = l_Int_Linear_Expr_renameVars(v_a_290_, v_f_237_);
                if v_isShared_294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_293_, 0, v___x_295_);
                    v___x_297_ = v___x_293_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_291_);
                    v___x_297_ = v_reuseFailAlloc_298_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_renameVars___boxed(
    mut v_e_300_: *mut crate::leanh::LeanObject,
    mut v_f_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l_Int_Linear_Expr_renameVars(v_e_300_, v_f_301_);
    crate::leanh::lean_dec_ref(v_f_301_);
    return v_res_302_;
}
pub unsafe fn l_Int_Linear_Poly_collectVars(
    mut v_p_303_: *mut crate::leanh::LeanObject,
    mut v_a_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_303_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_p_303_, 1);
                    return v_a_304_;
                } else {
                    v_v_305_ = crate::leanh::lean_ctor_get(v_p_303_, 1);
                    crate::leanh::lean_inc(v_v_305_);
                    v_p_306_ = crate::leanh::lean_ctor_get(v_p_303_, 2);
                    crate::leanh::lean_inc_ref(v_p_306_);
                    crate::leanh::lean_dec_ref_known(v_p_303_, 3);
                    v___x_307_ = l_Lean_Meta_Grind_collectVar(v_v_305_, v_a_304_);
                    v_p_303_ = v_p_306_;
                    v_a_304_ = v___x_307_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Expr_collectVars(
    mut v_e_309_: *mut crate::leanh::LeanObject,
    mut v_a_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_309_) {
                0 => {
                    crate::leanh::lean_dec_ref_known(v_e_309_, 1);
                    return v_a_310_;
                }
                1 => {
                    v_i_317_ = crate::leanh::lean_ctor_get(v_e_309_, 0);
                    crate::leanh::lean_inc(v_i_317_);
                    crate::leanh::lean_dec_ref_known(v_e_309_, 1);
                    v___x_318_ = l_Lean_Meta_Grind_collectVar(v_i_317_, v_a_310_);
                    return v___x_318_;
                }
                4 => {
                    v_a_319_ = crate::leanh::lean_ctor_get(v_e_309_, 0);
                    crate::leanh::lean_inc_ref(v_a_319_);
                    crate::leanh::lean_dec_ref_known(v_e_309_, 1);
                    v_e_309_ = v_a_319_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_a_321_ = crate::leanh::lean_ctor_get(v_e_309_, 1);
                    crate::leanh::lean_inc_ref(v_a_321_);
                    crate::leanh::lean_dec_ref_known(v_e_309_, 2);
                    v_e_309_ = v_a_321_;
                    state = 0;
                    continue;
                }
                6 => {
                    v_a_323_ = crate::leanh::lean_ctor_get(v_e_309_, 0);
                    crate::leanh::lean_inc_ref(v_a_323_);
                    crate::leanh::lean_dec_ref_known(v_e_309_, 2);
                    v_e_309_ = v_a_323_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_a_325_ = crate::leanh::lean_ctor_get(v_e_309_, 0);
                    crate::leanh::lean_inc_ref(v_a_325_);
                    v_b_326_ = crate::leanh::lean_ctor_get(v_e_309_, 1);
                    crate::leanh::lean_inc_ref(v_b_326_);
                    crate::leanh::lean_dec_ref(v_e_309_);
                    v_a_312_ = v_a_325_;
                    v_b_313_ = v_b_326_;
                    v___y_314_ = v_a_310_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_315_ = l_Int_Linear_Expr_collectVars(v_a_312_, v___y_314_);
                v_e_309_ = v_b_313_;
                v_a_310_ = v___x_315_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
}
