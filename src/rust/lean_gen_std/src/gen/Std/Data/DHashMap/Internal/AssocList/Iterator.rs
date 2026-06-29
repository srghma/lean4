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
pub static l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(
    mut v_it_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_140_) == 0 {
        let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_141_ = crate::leanh::lean_box(2);
        return v___x_141_;
    } else {
        let mut v_key_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_142_ = crate::leanh::lean_ctor_get(v_it_140_, 0);
        v_value_143_ = crate::leanh::lean_ctor_get(v_it_140_, 1);
        v_tail_144_ = crate::leanh::lean_ctor_get(v_it_140_, 2);
        crate::leanh::lean_inc(v_value_143_);
        crate::leanh::lean_inc(v_key_142_);
        v___x_145_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_145_, 0, v_key_142_);
        crate::leanh::lean_ctor_set(v___x_145_, 1, v_value_143_);
        crate::leanh::lean_inc(v_tail_144_);
        v___x_146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_146_, 0, v_tail_144_);
        crate::leanh::lean_ctor_set(v___x_146_, 1, v___x_145_);
        return v___x_146_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0___boxed(
    mut v_it_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_148_ =
        l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___lam__0(v_it_147_);
    crate::leanh::lean_dec(v_it_147_);
    return v_res_148_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma(
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_152_ = l_Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma___closed__0;
    return v___f_152_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter___redArg(
    mut v_it_153_: *mut crate::leanh::LeanObject,
    mut v_h__1_154_: *mut crate::leanh::LeanObject,
    mut v_h__2_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_153_) == 0 {
        let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_155_);
        v___x_156_ = crate::leanh::lean_box(0);
        v___x_157_ = crate::leanh::lean_apply_1(v_h__1_154_, v___x_156_);
        return v___x_157_;
    } else {
        let mut v_key_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_154_);
        v_key_158_ = crate::leanh::lean_ctor_get(v_it_153_, 0);
        crate::leanh::lean_inc(v_key_158_);
        v_value_159_ = crate::leanh::lean_ctor_get(v_it_153_, 1);
        crate::leanh::lean_inc(v_value_159_);
        v_tail_160_ = crate::leanh::lean_ctor_get(v_it_153_, 2);
        crate::leanh::lean_inc(v_tail_160_);
        crate::leanh::lean_dec_ref_known(v_it_153_, 3);
        v___x_161_ = crate::leanh::lean_apply_3(v_h__2_155_, v_key_158_, v_value_159_, v_tail_160_);
        return v___x_161_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__3_splitter(
    mut v_00_u03b1_162_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_163_: *mut crate::leanh::LeanObject,
    mut v_motive_164_: *mut crate::leanh::LeanObject,
    mut v_it_165_: *mut crate::leanh::LeanObject,
    mut v_h__1_166_: *mut crate::leanh::LeanObject,
    mut v_h__2_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_165_) == 0 {
        let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_167_);
        v___x_168_ = crate::leanh::lean_box(0);
        v___x_169_ = crate::leanh::lean_apply_1(v_h__1_166_, v___x_168_);
        return v___x_169_;
    } else {
        let mut v_key_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_166_);
        v_key_170_ = crate::leanh::lean_ctor_get(v_it_165_, 0);
        crate::leanh::lean_inc(v_key_170_);
        v_value_171_ = crate::leanh::lean_ctor_get(v_it_165_, 1);
        crate::leanh::lean_inc(v_value_171_);
        v_tail_172_ = crate::leanh::lean_ctor_get(v_it_165_, 2);
        crate::leanh::lean_inc(v_tail_172_);
        crate::leanh::lean_dec_ref_known(v_it_165_, 3);
        v___x_173_ = crate::leanh::lean_apply_3(v_h__2_167_, v_key_170_, v_value_171_, v_tail_172_);
        return v___x_173_;
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter___redArg(
    mut v_x_174_: *mut crate::leanh::LeanObject,
    mut v_h__1_175_: *mut crate::leanh::LeanObject,
    mut v_h__2_176_: *mut crate::leanh::LeanObject,
    mut v_h__3_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_174_) {
        0 => {
            let mut v_it_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_177_);
            crate::leanh::lean_dec(v_h__2_176_);
            v_it_178_ = crate::leanh::lean_ctor_get(v_x_174_, 0);
            crate::leanh::lean_inc(v_it_178_);
            v_out_179_ = crate::leanh::lean_ctor_get(v_x_174_, 1);
            crate::leanh::lean_inc(v_out_179_);
            crate::leanh::lean_dec_ref_known(v_x_174_, 2);
            v___x_180_ = crate::leanh::lean_apply_2(v_h__1_175_, v_it_178_, v_out_179_);
            return v___x_180_;
        }
        1 => {
            let mut v_it_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_177_);
            crate::leanh::lean_dec(v_h__1_175_);
            v_it_181_ = crate::leanh::lean_ctor_get(v_x_174_, 0);
            crate::leanh::lean_inc(v_it_181_);
            crate::leanh::lean_dec_ref_known(v_x_174_, 1);
            v___x_182_ = crate::leanh::lean_apply_1(v_h__2_176_, v_it_181_);
            return v___x_182_;
        }
        _ => {
            let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_176_);
            crate::leanh::lean_dec(v_h__1_175_);
            v___x_183_ = crate::leanh::lean_box(0);
            v___x_184_ = crate::leanh::lean_apply_1(v_h__3_177_, v___x_183_);
            return v___x_184_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_instIteratorAssocListIteratorIdSigma_match__1_splitter(
    mut v_00_u03b1_185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_186_: *mut crate::leanh::LeanObject,
    mut v_motive_187_: *mut crate::leanh::LeanObject,
    mut v_x_188_: *mut crate::leanh::LeanObject,
    mut v_h__1_189_: *mut crate::leanh::LeanObject,
    mut v_h__2_190_: *mut crate::leanh::LeanObject,
    mut v_h__3_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_188_) {
        0 => {
            let mut v_it_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_191_);
            crate::leanh::lean_dec(v_h__2_190_);
            v_it_192_ = crate::leanh::lean_ctor_get(v_x_188_, 0);
            crate::leanh::lean_inc(v_it_192_);
            v_out_193_ = crate::leanh::lean_ctor_get(v_x_188_, 1);
            crate::leanh::lean_inc(v_out_193_);
            crate::leanh::lean_dec_ref_known(v_x_188_, 2);
            v___x_194_ = crate::leanh::lean_apply_2(v_h__1_189_, v_it_192_, v_out_193_);
            return v___x_194_;
        }
        1 => {
            let mut v_it_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_191_);
            crate::leanh::lean_dec(v_h__1_189_);
            v_it_195_ = crate::leanh::lean_ctor_get(v_x_188_, 0);
            crate::leanh::lean_inc(v_it_195_);
            crate::leanh::lean_dec_ref_known(v_x_188_, 1);
            v___x_196_ = crate::leanh::lean_apply_1(v_h__2_190_, v_it_195_);
            return v___x_196_;
        }
        _ => {
            let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_190_);
            crate::leanh::lean_dec(v_h__1_189_);
            v___x_197_ = crate::leanh::lean_box(0);
            v___x_198_ = crate::leanh::lean_apply_1(v_h__3_191_, v___x_197_);
            return v___x_198_;
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Iterator_0__Std_DHashMap_Internal_AssocList_AssocListIterator_finitenessRelation(
    mut v_00_u03b1_199_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_201_ = crate::leanh::lean_box(0);
    return v___x_201_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0(
    mut v_toPure_202_: *mut crate::leanh::LeanObject,
    mut v_recur_203_: *mut crate::leanh::LeanObject,
    mut v_it_204_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_205_) == 0 {
        let mut v_a_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_204_);
        crate::leanh::lean_dec(v_recur_203_);
        v_a_206_ = crate::leanh::lean_ctor_get(v_____do__lift_205_, 0);
        crate::leanh::lean_inc(v_a_206_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_205_, 1);
        v___x_207_ = crate::leanh::lean_apply_2(v_toPure_202_, crate::leanh::lean_box(0), v_a_206_);
        return v___x_207_;
    } else {
        let mut v_a_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_202_);
        v_a_208_ = crate::leanh::lean_ctor_get(v_____do__lift_205_, 0);
        crate::leanh::lean_inc(v_a_208_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_205_, 1);
        v___x_209_ = crate::leanh::lean_apply_4(
            v_recur_203_,
            v_it_204_,
            v_a_208_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_209_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1(
    mut v_toPure_210_: *mut crate::leanh::LeanObject,
    mut v_recur_211_: *mut crate::leanh::LeanObject,
    mut v___y_212_: *mut crate::leanh::LeanObject,
    mut v_acc_213_: *mut crate::leanh::LeanObject,
    mut v_toBind_214_: *mut crate::leanh::LeanObject,
    mut v_s_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_215_) {
        0 => {
            let mut v_it_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_216_ = crate::leanh::lean_ctor_get(v_s_215_, 0);
            crate::leanh::lean_inc(v_it_216_);
            v_out_217_ = crate::leanh::lean_ctor_get(v_s_215_, 1);
            crate::leanh::lean_inc(v_out_217_);
            crate::leanh::lean_dec_ref_known(v_s_215_, 2);
            v___f_218_ = crate::leanh::lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
            crate::leanh::lean_closure_set(v___f_218_, 0, v_toPure_210_);
            crate::leanh::lean_closure_set(v___f_218_, 1, v_recur_211_);
            crate::leanh::lean_closure_set(v___f_218_, 2, v_it_216_);
            v___x_219_ = crate::leanh::lean_apply_3(
                v___y_212_,
                v_out_217_,
                crate::leanh::lean_box(0),
                v_acc_213_,
            );
            v___x_220_ = crate::leanh::lean_apply_4(
                v_toBind_214_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_219_,
                v___f_218_,
            );
            return v___x_220_;
        }
        1 => {
            let mut v_it_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_214_);
            crate::leanh::lean_dec(v___y_212_);
            crate::leanh::lean_dec(v_toPure_210_);
            v_it_221_ = crate::leanh::lean_ctor_get(v_s_215_, 0);
            crate::leanh::lean_inc(v_it_221_);
            crate::leanh::lean_dec_ref_known(v_s_215_, 1);
            v___x_222_ = crate::leanh::lean_apply_4(
                v_recur_211_,
                v_it_221_,
                v_acc_213_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_222_;
        }
        _ => {
            let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_214_);
            crate::leanh::lean_dec(v___y_212_);
            crate::leanh::lean_dec(v_recur_211_);
            v___x_223_ =
                crate::leanh::lean_apply_2(v_toPure_210_, crate::leanh::lean_box(0), v_acc_213_);
            return v___x_223_;
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(
    mut v_toPure_224_: *mut crate::leanh::LeanObject,
    mut v___y_225_: *mut crate::leanh::LeanObject,
    mut v_toBind_226_: *mut crate::leanh::LeanObject,
    mut v_lift_227_: *mut crate::leanh::LeanObject,
    mut v_it_228_: *mut crate::leanh::LeanObject,
    mut v_acc_229_: *mut crate::leanh::LeanObject,
    mut v_hP_230_: *mut crate::leanh::LeanObject,
    mut v_recur_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_232_ = crate::leanh::lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___f_232_, 0, v_toPure_224_);
    crate::leanh::lean_closure_set(v___f_232_, 1, v_recur_231_);
    crate::leanh::lean_closure_set(v___f_232_, 2, v___y_225_);
    crate::leanh::lean_closure_set(v___f_232_, 3, v_acc_229_);
    crate::leanh::lean_closure_set(v___f_232_, 4, v_toBind_226_);
    if crate::leanh::lean_obj_tag(v_it_228_) == 0 {
        let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_233_ = crate::leanh::lean_box(2);
        v___x_234_ = crate::leanh::lean_apply_4(
            v_lift_227_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_232_,
            v___x_233_,
        );
        return v___x_234_;
    } else {
        let mut v_key_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_235_ = crate::leanh::lean_ctor_get(v_it_228_, 0);
        v_value_236_ = crate::leanh::lean_ctor_get(v_it_228_, 1);
        v_tail_237_ = crate::leanh::lean_ctor_get(v_it_228_, 2);
        crate::leanh::lean_inc(v_value_236_);
        crate::leanh::lean_inc(v_key_235_);
        v___x_238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_238_, 0, v_key_235_);
        crate::leanh::lean_ctor_set(v___x_238_, 1, v_value_236_);
        crate::leanh::lean_inc(v_tail_237_);
        v___x_239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_239_, 0, v_tail_237_);
        crate::leanh::lean_ctor_set(v___x_239_, 1, v___x_238_);
        v___x_240_ = crate::leanh::lean_apply_4(
            v_lift_227_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_232_,
            v___x_239_,
        );
        return v___x_240_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed(
    mut v_toPure_241_: *mut crate::leanh::LeanObject,
    mut v___y_242_: *mut crate::leanh::LeanObject,
    mut v_toBind_243_: *mut crate::leanh::LeanObject,
    mut v_lift_244_: *mut crate::leanh::LeanObject,
    mut v_it_245_: *mut crate::leanh::LeanObject,
    mut v_acc_246_: *mut crate::leanh::LeanObject,
    mut v_hP_247_: *mut crate::leanh::LeanObject,
    mut v_recur_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2(v_toPure_241_, v___y_242_, v_toBind_243_, v_lift_244_, v_it_245_, v_acc_246_, v_hP_247_, v_recur_248_);
    crate::leanh::lean_dec(v_it_245_);
    return v_res_249_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3(
    mut v_inst_250_: *mut crate::leanh::LeanObject,
    mut v_lift_251_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_252_: *mut crate::leanh::LeanObject,
    mut v_Pl_253_: *mut crate::leanh::LeanObject,
    mut v_it_254_: *mut crate::leanh::LeanObject,
    mut v_init_255_: *mut crate::leanh::LeanObject,
    mut v___y_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_257_ = crate::leanh::lean_ctor_get(v_inst_250_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_257_);
    v_toBind_258_ = crate::leanh::lean_ctor_get(v_inst_250_, 1);
    crate::leanh::lean_inc(v_toBind_258_);
    crate::leanh::lean_dec_ref(v_inst_250_);
    v_toPure_259_ = crate::leanh::lean_ctor_get(v_toApplicative_257_, 1);
    crate::leanh::lean_inc(v_toPure_259_);
    crate::leanh::lean_dec_ref(v_toApplicative_257_);
    v___f_260_ = crate::leanh::lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_260_, 0, v_toPure_259_);
    crate::leanh::lean_closure_set(v___f_260_, 1, v___y_256_);
    crate::leanh::lean_closure_set(v___f_260_, 2, v_toBind_258_);
    crate::leanh::lean_closure_set(v___f_260_, 3, v_lift_251_);
    v___x_261_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_260_,
        v_it_254_,
        v_init_255_,
        crate::leanh::lean_box(0),
    );
    return v___x_261_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg(
    mut v_inst_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_263_ = crate::leanh::lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3 as *mut core::ffi::c_void, 7, 1);
    crate::leanh::lean_closure_set(v___f_263_, 0, v_inst_262_);
    return v___f_263_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad(
    mut v_00_u03b1_264_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_265_: *mut crate::leanh::LeanObject,
    mut v_m_266_: *mut crate::leanh::LeanObject,
    mut v_inst_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_268_ = crate::leanh::lean_alloc_closure(l_Std_DHashMap_Internal_AssocList_instIteratorLoopAssocListIteratorIdSigmaOfMonad___redArg___lam__3 as *mut core::ffi::c_void, 7, 1);
    crate::leanh::lean_closure_set(v___f_268_, 0, v_inst_267_);
    return v___f_268_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter___redArg(
    mut v_l_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_l_269_);
    return v_l_269_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter___redArg___boxed(
    mut v_l_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Std_DHashMap_Internal_AssocList_iter___redArg(v_l_270_);
    crate::leanh::lean_dec(v_l_270_);
    return v_res_271_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter(
    mut v_00_u03b1_272_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_273_: *mut crate::leanh::LeanObject,
    mut v_l_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_l_274_);
    return v_l_274_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_iter___boxed(
    mut v_00_u03b1_275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_276_: *mut crate::leanh::LeanObject,
    mut v_l_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l_Std_DHashMap_Internal_AssocList_iter(v_00_u03b1_275_, v_00_u03b2_276_, v_l_277_);
    crate::leanh::lean_dec(v_l_277_);
    return v_res_278_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(
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
pub unsafe fn initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
}
