// Lean compiler output
// Module: Std.Data.DHashMap.Internal.AssocList.Iterator
// Imports: Init.Data.Nat.Lemmas Init.Data.Iterators.Consumers Std.Data.DHashMap.Internal.AssocList.Basic
use crate::r#gen::Init::Data::Iterators::Consumers::{
    initialize_Init_Data_Iterators_Consumers, runtime_initialize_Init_Data_Iterators_Consumers,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
    runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0_value
) as *mut LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(
    mut v_it_140_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_140_) == 0 {
        let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
        v___x_141_ = lean_box(2);
        return v___x_141_;
    } else {
        let mut v_key_142_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_143_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
        v_key_142_ = lean_ctor_get(v_it_140_, 0);
        v_value_143_ = lean_ctor_get(v_it_140_, 1);
        v_tail_144_ = lean_ctor_get(v_it_140_, 2);
        lean_inc(v_value_143_);
        lean_inc(v_key_142_);
        v___x_145_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_145_, 0, v_key_142_);
        lean_ctor_set(v___x_145_, 1, v_value_143_);
        lean_inc(v_tail_144_);
        v___x_146_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_146_, 0, v_tail_144_);
        lean_ctor_set(v___x_146_, 1, v___x_145_);
        return v___x_146_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed(
    mut v_it_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_148_: *mut LeanObject = core::ptr::null_mut();
    v_res_148_ =
        l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(v_it_147_);
    lean_dec(v_it_147_);
    return v_res_148_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma(
    mut v_00_u03b1_150_: *mut LeanObject,
    mut v_00_u03b2_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_152_: *mut LeanObject = core::ptr::null_mut();
    v___f_152_ = l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0;
    return v___f_152_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter___redArg(
    mut v_it_153_: *mut LeanObject,
    mut v_h__1_154_: *mut LeanObject,
    mut v_h__2_155_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_153_) == 0 {
        let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_155_);
        v___x_156_ = lean_box(0);
        v___x_157_ = lean_apply_1(v_h__1_154_, v___x_156_);
        return v___x_157_;
    } else {
        let mut v_key_158_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_159_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_154_);
        v_key_158_ = lean_ctor_get(v_it_153_, 0);
        lean_inc(v_key_158_);
        v_value_159_ = lean_ctor_get(v_it_153_, 1);
        lean_inc(v_value_159_);
        v_tail_160_ = lean_ctor_get(v_it_153_, 2);
        lean_inc(v_tail_160_);
        lean_dec_ref_known(v_it_153_, 3);
        v___x_161_ = lean_apply_3(v_h__2_155_, v_key_158_, v_value_159_, v_tail_160_);
        return v___x_161_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter(
    mut v_00_u03b1_162_: *mut LeanObject,
    mut v_00_u03b2_163_: *mut LeanObject,
    mut v_motive_164_: *mut LeanObject,
    mut v_it_165_: *mut LeanObject,
    mut v_h__1_166_: *mut LeanObject,
    mut v_h__2_167_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_it_165_) == 0 {
        let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_167_);
        v___x_168_ = lean_box(0);
        v___x_169_ = lean_apply_1(v_h__1_166_, v___x_168_);
        return v___x_169_;
    } else {
        let mut v_key_170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_171_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_166_);
        v_key_170_ = lean_ctor_get(v_it_165_, 0);
        lean_inc(v_key_170_);
        v_value_171_ = lean_ctor_get(v_it_165_, 1);
        lean_inc(v_value_171_);
        v_tail_172_ = lean_ctor_get(v_it_165_, 2);
        lean_inc(v_tail_172_);
        lean_dec_ref_known(v_it_165_, 3);
        v___x_173_ = lean_apply_3(v_h__2_167_, v_key_170_, v_value_171_, v_tail_172_);
        return v___x_173_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter___redArg(
    mut v_x_174_: *mut LeanObject,
    mut v_h__1_175_: *mut LeanObject,
    mut v_h__2_176_: *mut LeanObject,
    mut v_h__3_177_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_174_) {
        0 => {
            let mut v_it_178_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_177_);
            lean_dec(v_h__2_176_);
            v_it_178_ = lean_ctor_get(v_x_174_, 0);
            lean_inc(v_it_178_);
            v_out_179_ = lean_ctor_get(v_x_174_, 1);
            lean_inc(v_out_179_);
            lean_dec_ref_known(v_x_174_, 2);
            v___x_180_ = lean_apply_2(v_h__1_175_, v_it_178_, v_out_179_);
            return v___x_180_;
        }
        1 => {
            let mut v_it_181_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_177_);
            lean_dec(v_h__1_175_);
            v_it_181_ = lean_ctor_get(v_x_174_, 0);
            lean_inc(v_it_181_);
            lean_dec_ref_known(v_x_174_, 1);
            v___x_182_ = lean_apply_1(v_h__2_176_, v_it_181_);
            return v___x_182_;
        }
        _ => {
            let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_176_);
            lean_dec(v_h__1_175_);
            v___x_183_ = lean_box(0);
            v___x_184_ = lean_apply_1(v_h__3_177_, v___x_183_);
            return v___x_184_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter(
    mut v_00_u03b1_185_: *mut LeanObject,
    mut v_00_u03b2_186_: *mut LeanObject,
    mut v_motive_187_: *mut LeanObject,
    mut v_x_188_: *mut LeanObject,
    mut v_h__1_189_: *mut LeanObject,
    mut v_h__2_190_: *mut LeanObject,
    mut v_h__3_191_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_188_) {
        0 => {
            let mut v_it_192_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_193_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_191_);
            lean_dec(v_h__2_190_);
            v_it_192_ = lean_ctor_get(v_x_188_, 0);
            lean_inc(v_it_192_);
            v_out_193_ = lean_ctor_get(v_x_188_, 1);
            lean_inc(v_out_193_);
            lean_dec_ref_known(v_x_188_, 2);
            v___x_194_ = lean_apply_2(v_h__1_189_, v_it_192_, v_out_193_);
            return v___x_194_;
        }
        1 => {
            let mut v_it_195_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_191_);
            lean_dec(v_h__1_189_);
            v_it_195_ = lean_ctor_get(v_x_188_, 0);
            lean_inc(v_it_195_);
            lean_dec_ref_known(v_x_188_, 1);
            v___x_196_ = lean_apply_1(v_h__2_190_, v_it_195_);
            return v___x_196_;
        }
        _ => {
            let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_190_);
            lean_dec(v_h__1_189_);
            v___x_197_ = lean_box(0);
            v___x_198_ = lean_apply_1(v_h__3_191_, v___x_197_);
            return v___x_198_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_AssocListIterator_finitenessRelation(
    mut v_00_u03b1_199_: *mut LeanObject,
    mut v_00_u03b2_200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    v___x_201_ = lean_box(0);
    return v___x_201_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0(
    mut v_toPure_202_: *mut LeanObject,
    mut v_recur_203_: *mut LeanObject,
    mut v_it_204_: *mut LeanObject,
    mut v_____do__lift_205_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_205_) == 0 {
        let mut v_a_206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_204_);
        lean_dec(v_recur_203_);
        v_a_206_ = lean_ctor_get(v_____do__lift_205_, 0);
        lean_inc(v_a_206_);
        lean_dec_ref_known(v_____do__lift_205_, 1);
        v___x_207_ = lean_apply_2(v_toPure_202_, lean_box(0), v_a_206_);
        return v___x_207_;
    } else {
        let mut v_a_208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_202_);
        v_a_208_ = lean_ctor_get(v_____do__lift_205_, 0);
        lean_inc(v_a_208_);
        lean_dec_ref_known(v_____do__lift_205_, 1);
        v___x_209_ = lean_apply_4(v_recur_203_, v_it_204_, v_a_208_, lean_box(0), lean_box(0));
        return v___x_209_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1(
    mut v_toPure_210_: *mut LeanObject,
    mut v_recur_211_: *mut LeanObject,
    mut v___y_212_: *mut LeanObject,
    mut v_acc_213_: *mut LeanObject,
    mut v_toBind_214_: *mut LeanObject,
    mut v_s_215_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_215_) {
        0 => {
            let mut v_it_216_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_217_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_218_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
            v_it_216_ = lean_ctor_get(v_s_215_, 0);
            lean_inc(v_it_216_);
            v_out_217_ = lean_ctor_get(v_s_215_, 1);
            lean_inc(v_out_217_);
            lean_dec_ref_known(v_s_215_, 2);
            v___f_218_ = lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
            lean_closure_set(v___f_218_, 0, v_toPure_210_);
            lean_closure_set(v___f_218_, 1, v_recur_211_);
            lean_closure_set(v___f_218_, 2, v_it_216_);
            v___x_219_ = lean_apply_3(v___y_212_, v_out_217_, lean_box(0), v_acc_213_);
            v___x_220_ = lean_apply_4(
                v_toBind_214_,
                lean_box(0),
                lean_box(0),
                v___x_219_,
                v___f_218_,
            );
            return v___x_220_;
        }
        1 => {
            let mut v_it_221_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_214_);
            lean_dec(v___y_212_);
            lean_dec(v_toPure_210_);
            v_it_221_ = lean_ctor_get(v_s_215_, 0);
            lean_inc(v_it_221_);
            lean_dec_ref_known(v_s_215_, 1);
            v___x_222_ = lean_apply_4(
                v_recur_211_,
                v_it_221_,
                v_acc_213_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_222_;
        }
        _ => {
            let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_214_);
            lean_dec(v___y_212_);
            lean_dec(v_recur_211_);
            v___x_223_ = lean_apply_2(v_toPure_210_, lean_box(0), v_acc_213_);
            return v___x_223_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(
    mut v_toPure_224_: *mut LeanObject,
    mut v___y_225_: *mut LeanObject,
    mut v_toBind_226_: *mut LeanObject,
    mut v_lift_227_: *mut LeanObject,
    mut v_it_228_: *mut LeanObject,
    mut v_acc_229_: *mut LeanObject,
    mut v_hP_230_: *mut LeanObject,
    mut v_recur_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_232_: *mut LeanObject = core::ptr::null_mut();
    v___f_232_ = lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_232_, 0, v_toPure_224_);
    lean_closure_set(v___f_232_, 1, v_recur_231_);
    lean_closure_set(v___f_232_, 2, v___y_225_);
    lean_closure_set(v___f_232_, 3, v_acc_229_);
    lean_closure_set(v___f_232_, 4, v_toBind_226_);
    if lean_obj_tag(v_it_228_) == 0 {
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        v___x_233_ = lean_box(2);
        v___x_234_ = lean_apply_4(
            v_lift_227_,
            lean_box(0),
            lean_box(0),
            v___f_232_,
            v___x_233_,
        );
        return v___x_234_;
    } else {
        let mut v_key_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        v_key_235_ = lean_ctor_get(v_it_228_, 0);
        v_value_236_ = lean_ctor_get(v_it_228_, 1);
        v_tail_237_ = lean_ctor_get(v_it_228_, 2);
        lean_inc(v_value_236_);
        lean_inc(v_key_235_);
        v___x_238_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_238_, 0, v_key_235_);
        lean_ctor_set(v___x_238_, 1, v_value_236_);
        lean_inc(v_tail_237_);
        v___x_239_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_239_, 0, v_tail_237_);
        lean_ctor_set(v___x_239_, 1, v___x_238_);
        v___x_240_ = lean_apply_4(
            v_lift_227_,
            lean_box(0),
            lean_box(0),
            v___f_232_,
            v___x_239_,
        );
        return v___x_240_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed(
    mut v_toPure_241_: *mut LeanObject,
    mut v___y_242_: *mut LeanObject,
    mut v_toBind_243_: *mut LeanObject,
    mut v_lift_244_: *mut LeanObject,
    mut v_it_245_: *mut LeanObject,
    mut v_acc_246_: *mut LeanObject,
    mut v_hP_247_: *mut LeanObject,
    mut v_recur_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_249_: *mut LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(v_toPure_241_, v___y_242_, v_toBind_243_, v_lift_244_, v_it_245_, v_acc_246_, v_hP_247_, v_recur_248_);
    lean_dec(v_it_245_);
    return v_res_249_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3(
    mut v_inst_250_: *mut LeanObject,
    mut v_lift_251_: *mut LeanObject,
    mut v_00_u03b3_252_: *mut LeanObject,
    mut v_Pl_253_: *mut LeanObject,
    mut v_it_254_: *mut LeanObject,
    mut v_init_255_: *mut LeanObject,
    mut v___y_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_257_ = lean_ctor_get(v_inst_250_, 0);
    lean_inc_ref(v_toApplicative_257_);
    v_toBind_258_ = lean_ctor_get(v_inst_250_, 1);
    lean_inc(v_toBind_258_);
    lean_dec_ref(v_inst_250_);
    v_toPure_259_ = lean_ctor_get(v_toApplicative_257_, 1);
    lean_inc(v_toPure_259_);
    lean_dec_ref(v_toApplicative_257_);
    v___f_260_ = lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void, 8, 4);
    lean_closure_set(v___f_260_, 0, v_toPure_259_);
    lean_closure_set(v___f_260_, 1, v___y_256_);
    lean_closure_set(v___f_260_, 2, v_toBind_258_);
    lean_closure_set(v___f_260_, 3, v_lift_251_);
    v___x_261_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_260_, v_it_254_, v_init_255_, lean_box(0));
    return v___x_261_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg(
    mut v_inst_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_263_: *mut LeanObject = core::ptr::null_mut();
    v___f_263_ = lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3 as *mut core::ffi::c_void, 7, 1);
    lean_closure_set(v___f_263_, 0, v_inst_262_);
    return v___f_263_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad(
    mut v_00_u03b1_264_: *mut LeanObject,
    mut v_00_u03b2_265_: *mut LeanObject,
    mut v_m_266_: *mut LeanObject,
    mut v_inst_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_268_: *mut LeanObject = core::ptr::null_mut();
    v___f_268_ = lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3 as *mut core::ffi::c_void, 7, 1);
    lean_closure_set(v___f_268_, 0, v_inst_267_);
    return v___f_268_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter___redArg(
    mut v_l_269_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_l_269_);
    return v_l_269_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter___redArg___boxed(
    mut v_l_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_271_: *mut LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Std_DHashMap_Internal_AssocList_iter___redArg(v_l_270_);
    lean_dec(v_l_270_);
    return v_res_271_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter(
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_00_u03b2_273_: *mut LeanObject,
    mut v_l_274_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_l_274_);
    return v_l_274_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter___boxed(
    mut v_00_u03b1_275_: *mut LeanObject,
    mut v_00_u03b2_276_: *mut LeanObject,
    mut v_l_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l_Std_DHashMap_Internal_AssocList_iter(v_00_u03b1_275_, v_00_u03b2_276_, v_l_277_);
    lean_dec(v_l_277_);
    return v_res_278_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
}
