// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Collect
// Imports: Init.Data.Iterators.Consumers.Partial Init.Data.Iterators.Consumers.Total Init.Data.Iterators.Consumers.Monadic.Collect
use crate::ffi::{lean_array_push, lean_array_to_list};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Partial::{
    initialize_Init_Data_Iterators_Consumers_Partial,
    runtime_initialize_Init_Data_Iterators_Consumers_Partial,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Total::{
    initialize_Init_Data_Iterators_Consumers_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Total,
};
use crate::r#gen::Init::WFExtrinsicFix::l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg;
pub static l_Std_Iter_toArray___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Iter_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iter_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Iter_toArray___redArg___lam__0(
    mut v_inst_148_: *mut crate::leanh::LeanObject,
    mut v_it_149_: *mut crate::leanh::LeanObject,
    mut v_acc_150_: *mut crate::leanh::LeanObject,
    mut v_recur_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_152_ = crate::leanh::lean_apply_1(v_inst_148_, v_it_149_);
    match crate::leanh::lean_obj_tag(v_val_152_) {
        0 => {
            let mut v_it_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_153_ = crate::leanh::lean_ctor_get(v_val_152_, 0);
            crate::leanh::lean_inc(v_it_153_);
            v_out_154_ = crate::leanh::lean_ctor_get(v_val_152_, 1);
            crate::leanh::lean_inc(v_out_154_);
            crate::leanh::lean_dec_ref_known(v_val_152_, 2);
            v___x_155_ = lean_array_push(v_acc_150_, v_out_154_);
            v___x_156_ = crate::leanh::lean_apply_3(
                v_recur_151_,
                v_it_153_,
                v___x_155_,
                crate::leanh::lean_box(0),
            );
            return v___x_156_;
        }
        1 => {
            let mut v_it_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_157_ = crate::leanh::lean_ctor_get(v_val_152_, 0);
            crate::leanh::lean_inc(v_it_157_);
            crate::leanh::lean_dec_ref_known(v_val_152_, 1);
            v___x_158_ = crate::leanh::lean_apply_3(
                v_recur_151_,
                v_it_157_,
                v_acc_150_,
                crate::leanh::lean_box(0),
            );
            return v___x_158_;
        }
        _ => {
            crate::leanh::lean_dec_ref(v_recur_151_);
            return v_acc_150_;
        }
    }
}
pub unsafe fn l_Std_Iter_toArray___redArg(
    mut v_inst_161_: *mut crate::leanh::LeanObject,
    mut v_it_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_163_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_163_, 0, v_inst_161_);
    v___x_164_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_165_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_163_, v_it_162_, v___x_164_,
    );
    return v___x_165_;
}
pub unsafe fn l_Std_Iter_toArray(
    mut v_00_u03b1_166_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_167_: *mut crate::leanh::LeanObject,
    mut v_inst_168_: *mut crate::leanh::LeanObject,
    mut v_it_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_170_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_170_, 0, v_inst_168_);
    v___x_171_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_172_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_170_, v_it_169_, v___x_171_,
    );
    return v___x_172_;
}
pub unsafe fn l_Std_Iter_Partial_toArray___redArg(
    mut v_inst_173_: *mut crate::leanh::LeanObject,
    mut v_it_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_175_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_175_, 0, v_inst_173_);
    v___x_176_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_177_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_175_, v_it_174_, v___x_176_,
    );
    return v___x_177_;
}
pub unsafe fn l_Std_Iter_Partial_toArray(
    mut v_00_u03b1_178_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_179_: *mut crate::leanh::LeanObject,
    mut v_inst_180_: *mut crate::leanh::LeanObject,
    mut v_it_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_182_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_182_, 0, v_inst_180_);
    v___x_183_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_184_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_182_, v_it_181_, v___x_183_,
    );
    return v___x_184_;
}
pub unsafe fn l_Std_Iter_Total_toArray___redArg(
    mut v_inst_185_: *mut crate::leanh::LeanObject,
    mut v_it_186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_187_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_187_, 0, v_inst_185_);
    v___x_188_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_189_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_187_, v_it_186_, v___x_188_,
    );
    return v___x_189_;
}
pub unsafe fn l_Std_Iter_Total_toArray(
    mut v_00_u03b1_190_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_191_: *mut crate::leanh::LeanObject,
    mut v_inst_192_: *mut crate::leanh::LeanObject,
    mut v_inst_193_: *mut crate::leanh::LeanObject,
    mut v_it_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_195_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_195_, 0, v_inst_192_);
    v___x_196_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_197_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_195_, v_it_194_, v___x_196_,
    );
    return v___x_197_;
}
pub unsafe fn l_Std_Iter_toListRev___redArg___lam__0(
    mut v_inst_198_: *mut crate::leanh::LeanObject,
    mut v_it_199_: *mut crate::leanh::LeanObject,
    mut v_acc_200_: *mut crate::leanh::LeanObject,
    mut v_recur_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_207_: u8 = 0;
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_212_: u8 = 0;
    let mut v_it_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_val_202_ = crate::leanh::lean_apply_1(v_inst_198_, v_it_199_);
                match crate::leanh::lean_obj_tag(v_val_202_) {
                    0 => {
                        v_it_203_ = crate::leanh::lean_ctor_get(v_val_202_, 0);
                        v_out_204_ = crate::leanh::lean_ctor_get(v_val_202_, 1);
                        v_isSharedCheck_212_ = (!crate::leanh::lean_is_exclusive(v_val_202_)) as u8;
                        if v_isSharedCheck_212_ == 0 {
                            v___x_206_ = v_val_202_;
                            v_isShared_207_ = v_isSharedCheck_212_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_out_204_);
                            crate::leanh::lean_inc(v_it_203_);
                            crate::leanh::lean_dec(v_val_202_);
                            v___x_206_ = crate::leanh::lean_box(0);
                            v_isShared_207_ = v_isSharedCheck_212_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_it_213_ = crate::leanh::lean_ctor_get(v_val_202_, 0);
                        crate::leanh::lean_inc(v_it_213_);
                        crate::leanh::lean_dec_ref_known(v_val_202_, 1);
                        v___x_214_ = crate::leanh::lean_apply_3(
                            v_recur_201_,
                            v_it_213_,
                            v_acc_200_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_214_;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_recur_201_);
                        return v_acc_200_;
                    }
                }
            }
            1 => {
                if v_isShared_207_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_206_, 1);
                    crate::leanh::lean_ctor_set(v___x_206_, 1, v_acc_200_);
                    crate::leanh::lean_ctor_set(v___x_206_, 0, v_out_204_);
                    v___x_209_ = v___x_206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_211_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_211_, 0, v_out_204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_211_, 1, v_acc_200_);
                    v___x_209_ = v_reuseFailAlloc_211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_210_ = crate::leanh::lean_apply_3(
                    v_recur_201_,
                    v_it_203_,
                    v___x_209_,
                    crate::leanh::lean_box(0),
                );
                return v___x_210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_toListRev___redArg(
    mut v_inst_215_: *mut crate::leanh::LeanObject,
    mut v_it_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_217_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_217_, 0, v_inst_215_);
    v___x_218_ = crate::leanh::lean_box(0);
    v___x_219_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_217_, v_it_216_, v___x_218_,
    );
    return v___x_219_;
}
pub unsafe fn l_Std_Iter_toListRev(
    mut v_00_u03b1_220_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_221_: *mut crate::leanh::LeanObject,
    mut v_inst_222_: *mut crate::leanh::LeanObject,
    mut v_it_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_224_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_224_, 0, v_inst_222_);
    v___x_225_ = crate::leanh::lean_box(0);
    v___x_226_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_224_, v_it_223_, v___x_225_,
    );
    return v___x_226_;
}
pub unsafe fn l_Std_Iter_Partial_toListRev___redArg(
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_it_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_229_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_229_, 0, v_inst_227_);
    v___x_230_ = crate::leanh::lean_box(0);
    v___x_231_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_229_, v_it_228_, v___x_230_,
    );
    return v___x_231_;
}
pub unsafe fn l_Std_Iter_Partial_toListRev(
    mut v_00_u03b1_232_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_233_: *mut crate::leanh::LeanObject,
    mut v_inst_234_: *mut crate::leanh::LeanObject,
    mut v_it_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_236_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_236_, 0, v_inst_234_);
    v___x_237_ = crate::leanh::lean_box(0);
    v___x_238_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_236_, v_it_235_, v___x_237_,
    );
    return v___x_238_;
}
pub unsafe fn l_Std_Iter_Total_toListRev___redArg(
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_it_240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_241_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_241_, 0, v_inst_239_);
    v___x_242_ = crate::leanh::lean_box(0);
    v___x_243_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_241_, v_it_240_, v___x_242_,
    );
    return v___x_243_;
}
pub unsafe fn l_Std_Iter_Total_toListRev(
    mut v_00_u03b1_244_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_245_: *mut crate::leanh::LeanObject,
    mut v_inst_246_: *mut crate::leanh::LeanObject,
    mut v_inst_247_: *mut crate::leanh::LeanObject,
    mut v_it_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_249_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_249_, 0, v_inst_246_);
    v___x_250_ = crate::leanh::lean_box(0);
    v___x_251_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_249_, v_it_248_, v___x_250_,
    );
    return v___x_251_;
}
pub unsafe fn l_Std_Iter_toList___redArg(
    mut v_inst_252_: *mut crate::leanh::LeanObject,
    mut v_it_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_254_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_254_, 0, v_inst_252_);
    v___x_255_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_256_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_254_, v_it_253_, v___x_255_,
    );
    v___x_257_ = lean_array_to_list(v___x_256_);
    return v___x_257_;
}
pub unsafe fn l_Std_Iter_toList(
    mut v_00_u03b1_258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_259_: *mut crate::leanh::LeanObject,
    mut v_inst_260_: *mut crate::leanh::LeanObject,
    mut v_it_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_262_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_262_, 0, v_inst_260_);
    v___x_263_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_264_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_262_, v_it_261_, v___x_263_,
    );
    v___x_265_ = lean_array_to_list(v___x_264_);
    return v___x_265_;
}
pub unsafe fn l_Std_Iter_Partial_toList___redArg(
    mut v_inst_266_: *mut crate::leanh::LeanObject,
    mut v_it_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_268_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_268_, 0, v_inst_266_);
    v___x_269_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_270_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_268_, v_it_267_, v___x_269_,
    );
    v___x_271_ = lean_array_to_list(v___x_270_);
    return v___x_271_;
}
pub unsafe fn l_Std_Iter_Partial_toList(
    mut v_00_u03b1_272_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_273_: *mut crate::leanh::LeanObject,
    mut v_inst_274_: *mut crate::leanh::LeanObject,
    mut v_it_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_276_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_276_, 0, v_inst_274_);
    v___x_277_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_278_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_276_, v_it_275_, v___x_277_,
    );
    v___x_279_ = lean_array_to_list(v___x_278_);
    return v___x_279_;
}
pub unsafe fn l_Std_Iter_Total_toList___redArg(
    mut v_inst_280_: *mut crate::leanh::LeanObject,
    mut v_it_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_282_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_282_, 0, v_inst_280_);
    v___x_283_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_282_, v_it_281_, v___x_283_,
    );
    v___x_285_ = lean_array_to_list(v___x_284_);
    return v___x_285_;
}
pub unsafe fn l_Std_Iter_Total_toList(
    mut v_00_u03b1_286_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_287_: *mut crate::leanh::LeanObject,
    mut v_inst_288_: *mut crate::leanh::LeanObject,
    mut v_inst_289_: *mut crate::leanh::LeanObject,
    mut v_it_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_291_ = crate::leanh::lean_alloc_closure(
        l_Std_Iter_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_291_, 0, v_inst_288_);
    v___x_292_ = l_Std_Iter_toArray___redArg___closed__0;
    v___x_293_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_291_, v_it_290_, v___x_292_,
    );
    v___x_294_ = lean_array_to_list(v___x_293_);
    return v___x_294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Collect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Collect(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Collect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Collect(builtin);
}
