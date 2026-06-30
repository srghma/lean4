// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Array
// Imports: Init.Data.Iterators.Consumers Init.Omega
use crate::ffi::{lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_lt};
use crate::r#gen::Init::Data::Iterators::Consumers::{
    initialize_Init_Data_Iterators_Consumers, runtime_initialize_Init_Data_Iterators_Consumers,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Array_iterFromIdxM___redArg(
    mut v_array_142_: *mut leanh::LeanObject,
    mut v_pos_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_144_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_144_, 0, v_array_142_);
    leanh::lean_ctor_set(v___x_144_, 1, v_pos_143_);
    return v___x_144_;
}
pub unsafe fn l_Array_iterFromIdxM(
    mut v_00_u03b1_145_: *mut leanh::LeanObject,
    mut v_array_146_: *mut leanh::LeanObject,
    mut v_m_147_: *mut leanh::LeanObject,
    mut v_pos_148_: *mut leanh::LeanObject,
    mut v_inst_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_150_, 0, v_array_146_);
    leanh::lean_ctor_set(v___x_150_, 1, v_pos_148_);
    return v___x_150_;
}
pub unsafe fn l_Array_iterFromIdxM___boxed(
    mut v_00_u03b1_151_: *mut leanh::LeanObject,
    mut v_array_152_: *mut leanh::LeanObject,
    mut v_m_153_: *mut leanh::LeanObject,
    mut v_pos_154_: *mut leanh::LeanObject,
    mut v_inst_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_156_ = l_Array_iterFromIdxM(
        v_00_u03b1_151_,
        v_array_152_,
        v_m_153_,
        v_pos_154_,
        v_inst_155_,
    );
    leanh::lean_dec(v_inst_155_);
    return v_res_156_;
}
pub unsafe fn l_Array_iterM___redArg(
    mut v_array_157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_158_ = leanh::lean_unsigned_to_nat(0);
    v___x_159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_159_, 0, v_array_157_);
    leanh::lean_ctor_set(v___x_159_, 1, v___x_158_);
    return v___x_159_;
}
pub unsafe fn l_Array_iterM(
    mut v_00_u03b1_160_: *mut leanh::LeanObject,
    mut v_array_161_: *mut leanh::LeanObject,
    mut v_m_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_164_ = leanh::lean_unsigned_to_nat(0);
    v___x_165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_165_, 0, v_array_161_);
    leanh::lean_ctor_set(v___x_165_, 1, v___x_164_);
    return v___x_165_;
}
pub unsafe fn l_Array_iterM___boxed(
    mut v_00_u03b1_166_: *mut leanh::LeanObject,
    mut v_array_167_: *mut leanh::LeanObject,
    mut v_m_168_: *mut leanh::LeanObject,
    mut v_inst_169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Array_iterM(v_00_u03b1_166_, v_array_167_, v_m_168_, v_inst_169_);
    leanh::lean_dec(v_inst_169_);
    return v_res_170_;
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0(
    mut v_inst_171_: *mut leanh::LeanObject,
    mut v_it_172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_177_: u8 = 0;
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: u8 = 0;
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_173_ = leanh::lean_ctor_get(v_it_172_, 0);
                v_pos_174_ = leanh::lean_ctor_get(v_it_172_, 1);
                v_isSharedCheck_190_ = (!leanh::lean_is_exclusive(v_it_172_)) as u8;
                if v_isSharedCheck_190_ == 0 {
                    v___x_176_ = v_it_172_;
                    v_isShared_177_ = v_isSharedCheck_190_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_pos_174_);
                    leanh::lean_inc(v_array_173_);
                    leanh::lean_dec(v_it_172_);
                    v___x_176_ = leanh::lean_box(0);
                    v_isShared_177_ = v_isSharedCheck_190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_178_ = lean_array_get_size(v_array_173_);
                v___x_179_ = lean_nat_dec_lt(v_pos_174_, v___x_178_);
                if v___x_179_ == 0 {
                    leanh::lean_del_object(v___x_176_);
                    leanh::lean_dec(v_pos_174_);
                    leanh::lean_dec_ref(v_array_173_);
                    v___x_180_ = leanh::lean_box(2);
                    v___x_181_ = leanh::lean_apply_2(
                        v_inst_171_,
                        leanh::lean_box(0),
                        v___x_180_,
                    );
                    return v___x_181_;
                } else {
                    v___x_182_ = leanh::lean_unsigned_to_nat(1);
                    v___x_183_ = lean_nat_add(v_pos_174_, v___x_182_);
                    leanh::lean_inc_ref(v_array_173_);
                    if v_isShared_177_ == 0 {
                        leanh::lean_ctor_set(v___x_176_, 1, v___x_183_);
                        v___x_185_ = v___x_176_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_189_, 0, v_array_173_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_183_);
                        v___x_185_ = v_reuseFailAlloc_189_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_186_ = lean_array_fget(v_array_173_, v_pos_174_);
                leanh::lean_dec(v_pos_174_);
                leanh::lean_dec_ref(v_array_173_);
                v___x_187_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_187_, 0, v___x_185_);
                leanh::lean_ctor_set(v___x_187_, 1, v___x_186_);
                v___x_188_ =
                    leanh::lean_apply_2(v_inst_171_, leanh::lean_box(0), v___x_187_);
                return v___x_188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIterator___redArg(
    mut v_inst_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_192_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_192_, 0, v_inst_191_);
    return v___f_192_;
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIterator(
    mut v_m_193_: *mut leanh::LeanObject,
    mut v_00_u03b1_194_: *mut leanh::LeanObject,
    mut v_inst_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_196_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_196_, 0, v_inst_195_);
    return v___f_196_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(
    mut v_00_u03b1_197_: *mut leanh::LeanObject,
    mut v_m_198_: *mut leanh::LeanObject,
    mut v_inst_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_200_ = leanh::lean_box(0);
    return v___x_200_;
}
pub unsafe fn l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_201_: *mut leanh::LeanObject,
    mut v_m_202_: *mut leanh::LeanObject,
    mut v_inst_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(v_00_u03b1_201_, v_m_202_, v_inst_203_);
    leanh::lean_dec(v_inst_203_);
    return v_res_204_;
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_205_: *mut leanh::LeanObject,
    mut v_recur_206_: *mut leanh::LeanObject,
    mut v_it_207_: *mut leanh::LeanObject,
    mut v_____do__lift_208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_208_) == 0 {
        let mut v_a_209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_it_207_);
        leanh::lean_dec(v_recur_206_);
        v_a_209_ = leanh::lean_ctor_get(v_____do__lift_208_, 0);
        leanh::lean_inc(v_a_209_);
        leanh::lean_dec_ref_known(v_____do__lift_208_, 1);
        v___x_210_ = leanh::lean_apply_2(v_toPure_205_, leanh::lean_box(0), v_a_209_);
        return v___x_210_;
    } else {
        let mut v_a_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_205_);
        v_a_211_ = leanh::lean_ctor_get(v_____do__lift_208_, 0);
        leanh::lean_inc(v_a_211_);
        leanh::lean_dec_ref_known(v_____do__lift_208_, 1);
        v___x_212_ = leanh::lean_apply_4(
            v_recur_206_,
            v_it_207_,
            v_a_211_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_212_;
    }
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_213_: *mut leanh::LeanObject,
    mut v_recur_214_: *mut leanh::LeanObject,
    mut v___y_215_: *mut leanh::LeanObject,
    mut v_acc_216_: *mut leanh::LeanObject,
    mut v_toBind_217_: *mut leanh::LeanObject,
    mut v_s_218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_218_) {
        0 => {
            let mut v_it_219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_219_ = leanh::lean_ctor_get(v_s_218_, 0);
            leanh::lean_inc(v_it_219_);
            v_out_220_ = leanh::lean_ctor_get(v_s_218_, 1);
            leanh::lean_inc(v_out_220_);
            leanh::lean_dec_ref_known(v_s_218_, 2);
            v___f_221_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_221_, 0, v_toPure_213_);
            leanh::lean_closure_set(v___f_221_, 1, v_recur_214_);
            leanh::lean_closure_set(v___f_221_, 2, v_it_219_);
            v___x_222_ = leanh::lean_apply_3(
                v___y_215_,
                v_out_220_,
                leanh::lean_box(0),
                v_acc_216_,
            );
            v___x_223_ = leanh::lean_apply_4(
                v_toBind_217_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_222_,
                v___f_221_,
            );
            return v___x_223_;
        }
        1 => {
            let mut v_it_224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_217_);
            leanh::lean_dec(v___y_215_);
            leanh::lean_dec(v_toPure_213_);
            v_it_224_ = leanh::lean_ctor_get(v_s_218_, 0);
            leanh::lean_inc(v_it_224_);
            leanh::lean_dec_ref_known(v_s_218_, 1);
            v___x_225_ = leanh::lean_apply_4(
                v_recur_214_,
                v_it_224_,
                v_acc_216_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_225_;
        }
        _ => {
            let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_217_);
            leanh::lean_dec(v___y_215_);
            leanh::lean_dec(v_recur_214_);
            v___x_226_ =
                leanh::lean_apply_2(v_toPure_213_, leanh::lean_box(0), v_acc_216_);
            return v___x_226_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_227_: *mut leanh::LeanObject,
    mut v___y_228_: *mut leanh::LeanObject,
    mut v_toBind_229_: *mut leanh::LeanObject,
    mut v_toPure_230_: *mut leanh::LeanObject,
    mut v_lift_231_: *mut leanh::LeanObject,
    mut v_it_232_: *mut leanh::LeanObject,
    mut v_acc_233_: *mut leanh::LeanObject,
    mut v_hP_234_: *mut leanh::LeanObject,
    mut v_recur_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v___f_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: u8 = 0;
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_236_ = leanh::lean_ctor_get(v_it_232_, 0);
                v_pos_237_ = leanh::lean_ctor_get(v_it_232_, 1);
                v_isSharedCheck_256_ = (!leanh::lean_is_exclusive(v_it_232_)) as u8;
                if v_isSharedCheck_256_ == 0 {
                    v___x_239_ = v_it_232_;
                    v_isShared_240_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_pos_237_);
                    leanh::lean_inc(v_array_236_);
                    leanh::lean_dec(v_it_232_);
                    v___x_239_ = leanh::lean_box(0);
                    v_isShared_240_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_241_ = leanh::lean_alloc_closure(
                    l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___f_241_, 0, v_toPure_227_);
                leanh::lean_closure_set(v___f_241_, 1, v_recur_235_);
                leanh::lean_closure_set(v___f_241_, 2, v___y_228_);
                leanh::lean_closure_set(v___f_241_, 3, v_acc_233_);
                leanh::lean_closure_set(v___f_241_, 4, v_toBind_229_);
                v___x_242_ = lean_array_get_size(v_array_236_);
                v___x_243_ = lean_nat_dec_lt(v_pos_237_, v___x_242_);
                if v___x_243_ == 0 {
                    leanh::lean_del_object(v___x_239_);
                    leanh::lean_dec(v_pos_237_);
                    leanh::lean_dec_ref(v_array_236_);
                    v___x_244_ = leanh::lean_box(2);
                    v___x_245_ = leanh::lean_apply_2(
                        v_toPure_230_,
                        leanh::lean_box(0),
                        v___x_244_,
                    );
                    v___x_246_ = leanh::lean_apply_4(
                        v_lift_231_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_241_,
                        v___x_245_,
                    );
                    return v___x_246_;
                } else {
                    v___x_247_ = leanh::lean_unsigned_to_nat(1);
                    v___x_248_ = lean_nat_add(v_pos_237_, v___x_247_);
                    leanh::lean_inc_ref(v_array_236_);
                    if v_isShared_240_ == 0 {
                        leanh::lean_ctor_set(v___x_239_, 1, v___x_248_);
                        v___x_250_ = v___x_239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_255_, 0, v_array_236_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_248_);
                        v___x_250_ = v_reuseFailAlloc_255_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_251_ = lean_array_fget(v_array_236_, v_pos_237_);
                leanh::lean_dec(v_pos_237_);
                leanh::lean_dec_ref(v_array_236_);
                v___x_252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_252_, 0, v___x_250_);
                leanh::lean_ctor_set(v___x_252_, 1, v___x_251_);
                v___x_253_ = leanh::lean_apply_2(
                    v_toPure_230_,
                    leanh::lean_box(0),
                    v___x_252_,
                );
                v___x_254_ = leanh::lean_apply_4(
                    v_lift_231_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_241_,
                    v___x_253_,
                );
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_257_: *mut leanh::LeanObject,
    mut v_toPure_258_: *mut leanh::LeanObject,
    mut v_lift_259_: *mut leanh::LeanObject,
    mut v_00_u03b3_260_: *mut leanh::LeanObject,
    mut v_Pl_261_: *mut leanh::LeanObject,
    mut v_it_262_: *mut leanh::LeanObject,
    mut v_init_263_: *mut leanh::LeanObject,
    mut v___y_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_265_ = leanh::lean_ctor_get(v_inst_257_, 0);
    leanh::lean_inc_ref(v_toApplicative_265_);
    v_toBind_266_ = leanh::lean_ctor_get(v_inst_257_, 1);
    leanh::lean_inc(v_toBind_266_);
    leanh::lean_dec_ref(v_inst_257_);
    v_toPure_267_ = leanh::lean_ctor_get(v_toApplicative_265_, 1);
    leanh::lean_inc(v_toPure_267_);
    leanh::lean_dec_ref(v_toApplicative_265_);
    v___f_268_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    leanh::lean_closure_set(v___f_268_, 0, v_toPure_267_);
    leanh::lean_closure_set(v___f_268_, 1, v___y_264_);
    leanh::lean_closure_set(v___f_268_, 2, v_toBind_266_);
    leanh::lean_closure_set(v___f_268_, 3, v_toPure_258_);
    leanh::lean_closure_set(v___f_268_, 4, v_lift_259_);
    v___x_269_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_268_,
        v_it_262_,
        v_init_263_,
        leanh::lean_box(0),
    );
    return v___x_269_;
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg(
    mut v_inst_270_: *mut leanh::LeanObject,
    mut v_inst_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_272_ = leanh::lean_ctor_get(v_inst_270_, 0);
    leanh::lean_inc_ref(v_toApplicative_272_);
    leanh::lean_dec_ref(v_inst_270_);
    v_toPure_273_ = leanh::lean_ctor_get(v_toApplicative_272_, 1);
    leanh::lean_inc(v_toPure_273_);
    leanh::lean_dec_ref(v_toApplicative_272_);
    v___f_274_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___f_274_, 0, v_inst_271_);
    leanh::lean_closure_set(v___f_274_, 1, v_toPure_273_);
    return v___f_274_;
}
pub unsafe fn l_Std_Iterators_Types_ArrayIterator_instIteratorLoop(
    mut v_m_275_: *mut leanh::LeanObject,
    mut v_00_u03b1_276_: *mut leanh::LeanObject,
    mut v_inst_277_: *mut leanh::LeanObject,
    mut v_n_278_: *mut leanh::LeanObject,
    mut v_inst_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_280_ = leanh::lean_ctor_get(v_inst_277_, 0);
    leanh::lean_inc_ref(v_toApplicative_280_);
    leanh::lean_dec_ref(v_inst_277_);
    v_toPure_281_ = leanh::lean_ctor_get(v_toApplicative_280_, 1);
    leanh::lean_inc(v_toPure_281_);
    leanh::lean_dec_ref(v_toApplicative_280_);
    v___f_282_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___f_282_, 0, v_inst_279_);
    leanh::lean_closure_set(v___f_282_, 1, v_toPure_281_);
    return v___f_282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Monadic_Array(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Monadic_Array(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
}