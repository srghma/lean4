// Lean compiler output
// Module: Init.Data.Queue
// Imports: Init.Data.List.Control
use crate::ffi::lean_array_mk;
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, l_List_filterAuxM___redArg,
    runtime_initialize_Init_Data_List_Control,
};
pub static l_Std_Queue_empty___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Queue_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Queue_empty___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Queue_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Queue_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Queue_empty(
    mut v_00_u03b1_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_161_ = l_Std_Queue_empty___closed__0;
    return v___x_161_;
}
pub unsafe fn _init_l_Std_Queue_instEmptyCollection___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_162_ = l_Std_Queue_empty(leanh::lean_box(0));
    return v___x_162_;
}
pub unsafe fn l_Std_Queue_instEmptyCollection(
    mut v_00_u03b1_163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_164_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Queue_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_Queue_instEmptyCollection___closed__0_once),
        _init_l_Std_Queue_instEmptyCollection___closed__0,
    );
    return v___x_164_;
}
pub unsafe fn l_Std_Queue_instInhabited(
    mut v_00_u03b1_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Queue_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_Queue_instEmptyCollection___closed__0_once),
        _init_l_Std_Queue_instEmptyCollection___closed__0,
    );
    return v___x_166_;
}
pub unsafe fn l_Std_Queue_isEmpty___redArg(mut v_q_167_: *mut leanh::LeanObject) -> u8 {
    let mut v_eList_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: u8 = 0;
    v_eList_168_ = leanh::lean_ctor_get(v_q_167_, 0);
    v_dList_169_ = leanh::lean_ctor_get(v_q_167_, 1);
    v___x_170_ = l_List_isEmpty___redArg(v_dList_169_);
    if v___x_170_ == 0 {
        return v___x_170_;
    } else {
        let mut v___x_171_: u8 = 0;
        v___x_171_ = l_List_isEmpty___redArg(v_eList_168_);
        return v___x_171_;
    }
}
pub unsafe fn l_Std_Queue_isEmpty___redArg___boxed(
    mut v_q_172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_173_: u8 = 0;
    let mut v_r_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_173_ = l_Std_Queue_isEmpty___redArg(v_q_172_);
    leanh::lean_dec_ref(v_q_172_);
    v_r_174_ = leanh::lean_box((v_res_173_) as usize);
    return v_r_174_;
}
pub unsafe fn l_Std_Queue_isEmpty(
    mut v_00_u03b1_175_: *mut leanh::LeanObject,
    mut v_q_176_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_177_: u8 = 0;
    v___x_177_ = l_Std_Queue_isEmpty___redArg(v_q_176_);
    return v___x_177_;
}
pub unsafe fn l_Std_Queue_isEmpty___boxed(
    mut v_00_u03b1_178_: *mut leanh::LeanObject,
    mut v_q_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_180_: u8 = 0;
    let mut v_r_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l_Std_Queue_isEmpty(v_00_u03b1_178_, v_q_179_);
    leanh::lean_dec_ref(v_q_179_);
    v_r_181_ = leanh::lean_box((v_res_180_) as usize);
    return v_r_181_;
}
pub unsafe fn l_Std_Queue_enqueue___redArg(
    mut v_v_182_: *mut leanh::LeanObject,
    mut v_q_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eList_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_188_: u8 = 0;
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eList_184_ = leanh::lean_ctor_get(v_q_183_, 0);
                v_dList_185_ = leanh::lean_ctor_get(v_q_183_, 1);
                v_isSharedCheck_193_ = (!leanh::lean_is_exclusive(v_q_183_)) as u8;
                if v_isSharedCheck_193_ == 0 {
                    v___x_187_ = v_q_183_;
                    v_isShared_188_ = v_isSharedCheck_193_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_dList_185_);
                    leanh::lean_inc(v_eList_184_);
                    leanh::lean_dec(v_q_183_);
                    v___x_187_ = leanh::lean_box(0);
                    v_isShared_188_ = v_isSharedCheck_193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_189_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_189_, 0, v_v_182_);
                leanh::lean_ctor_set(v___x_189_, 1, v_eList_184_);
                if v_isShared_188_ == 0 {
                    leanh::lean_ctor_set(v___x_187_, 0, v___x_189_);
                    v___x_191_ = v___x_187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_192_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_192_, 1, v_dList_185_);
                    v___x_191_ = v_reuseFailAlloc_192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_enqueue(
    mut v_00_u03b1_194_: *mut leanh::LeanObject,
    mut v_v_195_: *mut leanh::LeanObject,
    mut v_q_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = l_Std_Queue_enqueue___redArg(v_v_195_, v_q_196_);
    return v___x_197_;
}
pub unsafe fn l_Std_Queue_enqueueAll___redArg(
    mut v_vs_198_: *mut leanh::LeanObject,
    mut v_q_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eList_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_204_: u8 = 0;
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eList_200_ = leanh::lean_ctor_get(v_q_199_, 0);
                v_dList_201_ = leanh::lean_ctor_get(v_q_199_, 1);
                v_isSharedCheck_209_ = (!leanh::lean_is_exclusive(v_q_199_)) as u8;
                if v_isSharedCheck_209_ == 0 {
                    v___x_203_ = v_q_199_;
                    v_isShared_204_ = v_isSharedCheck_209_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_dList_201_);
                    leanh::lean_inc(v_eList_200_);
                    leanh::lean_dec(v_q_199_);
                    v___x_203_ = leanh::lean_box(0);
                    v_isShared_204_ = v_isSharedCheck_209_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_205_ = l_List_appendTR___redArg(v_vs_198_, v_eList_200_);
                if v_isShared_204_ == 0 {
                    leanh::lean_ctor_set(v___x_203_, 0, v___x_205_);
                    v___x_207_ = v___x_203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_208_, 1, v_dList_201_);
                    v___x_207_ = v_reuseFailAlloc_208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_enqueueAll(
    mut v_00_u03b1_210_: *mut leanh::LeanObject,
    mut v_vs_211_: *mut leanh::LeanObject,
    mut v_q_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_213_ = l_Std_Queue_enqueueAll___redArg(v_vs_211_, v_q_212_);
    return v___x_213_;
}
pub unsafe fn l_Std_Queue_dequeue_x3f___redArg(
    mut v_q_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dList_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eList_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_219_: u8 = 0;
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_226_: u8 = 0;
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut v_isSharedCheck_235_: u8 = 0;
    let mut v_unused_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eList_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v_head_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_245_: u8 = 0;
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_253_: u8 = 0;
    let mut v_isSharedCheck_254_: u8 = 0;
    let mut v_unused_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dList_215_ = leanh::lean_ctor_get(v_q_214_, 1);
                leanh::lean_inc(v_dList_215_);
                if leanh::lean_obj_tag(v_dList_215_) == 0 {
                    v_eList_216_ = leanh::lean_ctor_get(v_q_214_, 0);
                    v_isSharedCheck_235_ = (!leanh::lean_is_exclusive(v_q_214_)) as u8;
                    if v_isSharedCheck_235_ == 0 {
                        v_unused_236_ = leanh::lean_ctor_get(v_q_214_, 1);
                        leanh::lean_dec(v_unused_236_);
                        v___x_218_ = v_q_214_;
                        v_isShared_219_ = v_isSharedCheck_235_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_eList_216_);
                        leanh::lean_dec(v_q_214_);
                        v___x_218_ = leanh::lean_box(0);
                        v_isShared_219_ = v_isSharedCheck_235_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_eList_237_ = leanh::lean_ctor_get(v_q_214_, 0);
                    v_isSharedCheck_254_ = (!leanh::lean_is_exclusive(v_q_214_)) as u8;
                    if v_isSharedCheck_254_ == 0 {
                        v_unused_255_ = leanh::lean_ctor_get(v_q_214_, 1);
                        leanh::lean_dec(v_unused_255_);
                        v___x_239_ = v_q_214_;
                        v_isShared_240_ = v_isSharedCheck_254_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_eList_237_);
                        leanh::lean_dec(v_q_214_);
                        v___x_239_ = leanh::lean_box(0);
                        v_isShared_240_ = v_isSharedCheck_254_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_220_ = l_List_reverse___redArg(v_eList_216_);
                if leanh::lean_obj_tag(v___x_220_) == 0 {
                    leanh::lean_del_object(v___x_218_);
                    v___x_221_ = leanh::lean_box(0);
                    return v___x_221_;
                } else {
                    v_head_222_ = leanh::lean_ctor_get(v___x_220_, 0);
                    v_tail_223_ = leanh::lean_ctor_get(v___x_220_, 1);
                    v_isSharedCheck_234_ = (!leanh::lean_is_exclusive(v___x_220_)) as u8;
                    if v_isSharedCheck_234_ == 0 {
                        v___x_225_ = v___x_220_;
                        v_isShared_226_ = v_isSharedCheck_234_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_223_);
                        leanh::lean_inc(v_head_222_);
                        leanh::lean_dec(v___x_220_);
                        v___x_225_ = leanh::lean_box(0);
                        v_isShared_226_ = v_isSharedCheck_234_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_219_ == 0 {
                    leanh::lean_ctor_set(v___x_218_, 1, v_tail_223_);
                    leanh::lean_ctor_set(v___x_218_, 0, v_dList_215_);
                    v___x_228_ = v___x_218_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_233_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_233_, 0, v_dList_215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_233_, 1, v_tail_223_);
                    v___x_228_ = v_reuseFailAlloc_233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_226_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_225_, 0);
                    leanh::lean_ctor_set(v___x_225_, 1, v___x_228_);
                    v___x_230_ = v___x_225_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_232_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 0, v_head_222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_228_);
                    v___x_230_ = v_reuseFailAlloc_232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_231_, 0, v___x_230_);
                return v___x_231_;
            }
            5 => {
                v_head_241_ = leanh::lean_ctor_get(v_dList_215_, 0);
                v_tail_242_ = leanh::lean_ctor_get(v_dList_215_, 1);
                v_isSharedCheck_253_ = (!leanh::lean_is_exclusive(v_dList_215_)) as u8;
                if v_isSharedCheck_253_ == 0 {
                    v___x_244_ = v_dList_215_;
                    v_isShared_245_ = v_isSharedCheck_253_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_tail_242_);
                    leanh::lean_inc(v_head_241_);
                    leanh::lean_dec(v_dList_215_);
                    v___x_244_ = leanh::lean_box(0);
                    v_isShared_245_ = v_isSharedCheck_253_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_240_ == 0 {
                    leanh::lean_ctor_set(v___x_239_, 1, v_tail_242_);
                    v___x_247_ = v___x_239_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_252_, 0, v_eList_237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_252_, 1, v_tail_242_);
                    v___x_247_ = v_reuseFailAlloc_252_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_245_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_244_, 0);
                    leanh::lean_ctor_set(v___x_244_, 1, v___x_247_);
                    v___x_249_ = v___x_244_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_251_, 0, v_head_241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_251_, 1, v___x_247_);
                    v___x_249_ = v_reuseFailAlloc_251_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_250_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_250_, 0, v___x_249_);
                return v___x_250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_dequeue_x3f(
    mut v_00_u03b1_256_: *mut leanh::LeanObject,
    mut v_q_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = l_Std_Queue_dequeue_x3f___redArg(v_q_257_);
    return v___x_258_;
}
pub unsafe fn l_Std_Queue_toArray___redArg(
    mut v_q_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eList_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eList_260_ = leanh::lean_ctor_get(v_q_259_, 0);
    leanh::lean_inc(v_eList_260_);
    v_dList_261_ = leanh::lean_ctor_get(v_q_259_, 1);
    leanh::lean_inc(v_dList_261_);
    leanh::lean_dec_ref(v_q_259_);
    v___x_262_ = lean_array_mk(v_dList_261_);
    v___x_263_ = lean_array_mk(v_eList_260_);
    v___x_264_ = l_Array_reverse___redArg(v___x_263_);
    v___x_265_ = l_Array_append___redArg(v___x_262_, v___x_264_);
    leanh::lean_dec_ref(v___x_264_);
    return v___x_265_;
}
pub unsafe fn l_Std_Queue_toArray(
    mut v_00_u03b1_266_: *mut leanh::LeanObject,
    mut v_q_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Std_Queue_toArray___redArg(v_q_267_);
    return v___x_268_;
}
pub unsafe fn l_Std_Queue_filterM___redArg___lam__0(
    mut v_dList_269_: *mut leanh::LeanObject,
    mut v_toPure_270_: *mut leanh::LeanObject,
    mut v_eList_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_272_: u8 = 0;
    v___x_272_ = l_List_isEmpty___redArg(v_dList_269_);
    if v___x_272_ == 0 {
        let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_273_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_273_, 0, v_eList_271_);
        leanh::lean_ctor_set(v___x_273_, 1, v_dList_269_);
        v___x_274_ =
            leanh::lean_apply_2(v_toPure_270_, leanh::lean_box(0), v___x_273_);
        return v___x_274_;
    } else {
        let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_dList_269_);
        v___x_275_ = leanh::lean_box(0);
        v___x_276_ = l_List_reverse___redArg(v_eList_271_);
        v___x_277_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_277_, 0, v___x_275_);
        leanh::lean_ctor_set(v___x_277_, 1, v___x_276_);
        v___x_278_ =
            leanh::lean_apply_2(v_toPure_270_, leanh::lean_box(0), v___x_277_);
        return v___x_278_;
    }
}
pub unsafe fn l_Std_Queue_filterM___redArg___lam__1(
    mut v_toPure_279_: *mut leanh::LeanObject,
    mut v_as_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = l_List_reverse___redArg(v_as_280_);
    v___x_282_ = leanh::lean_apply_2(v_toPure_279_, leanh::lean_box(0), v___x_281_);
    return v___x_282_;
}
pub unsafe fn l_Std_Queue_filterM___redArg___lam__2(
    mut v_toPure_283_: *mut leanh::LeanObject,
    mut v_inst_284_: *mut leanh::LeanObject,
    mut v_p_285_: *mut leanh::LeanObject,
    mut v_eList_286_: *mut leanh::LeanObject,
    mut v_toBind_287_: *mut leanh::LeanObject,
    mut v_dList_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toPure_283_);
    v___f_289_ = leanh::lean_alloc_closure(
        l_Std_Queue_filterM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_289_, 0, v_dList_288_);
    leanh::lean_closure_set(v___f_289_, 1, v_toPure_283_);
    v___x_290_ = leanh::lean_box(0);
    v___x_291_ = l_List_filterAuxM___redArg(v_inst_284_, v_p_285_, v_eList_286_, v___x_290_);
    v___f_292_ = leanh::lean_alloc_closure(
        l_Std_Queue_filterM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_292_, 0, v_toPure_283_);
    leanh::lean_inc(v_toBind_287_);
    v___x_293_ = leanh::lean_apply_4(
        v_toBind_287_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_291_,
        v___f_292_,
    );
    v___x_294_ = leanh::lean_apply_4(
        v_toBind_287_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_293_,
        v___f_289_,
    );
    return v___x_294_;
}
pub unsafe fn l_Std_Queue_filterM___redArg(
    mut v_inst_295_: *mut leanh::LeanObject,
    mut v_p_296_: *mut leanh::LeanObject,
    mut v_q_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eList_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_298_ = leanh::lean_ctor_get(v_inst_295_, 0);
    v_toBind_299_ = leanh::lean_ctor_get(v_inst_295_, 1);
    leanh::lean_inc_n(v_toBind_299_, 3);
    v_eList_300_ = leanh::lean_ctor_get(v_q_297_, 0);
    leanh::lean_inc(v_eList_300_);
    v_dList_301_ = leanh::lean_ctor_get(v_q_297_, 1);
    leanh::lean_inc(v_dList_301_);
    leanh::lean_dec_ref(v_q_297_);
    v_toPure_302_ = leanh::lean_ctor_get(v_toApplicative_298_, 1);
    leanh::lean_inc_n(v_toPure_302_, 2);
    leanh::lean_inc(v_p_296_);
    leanh::lean_inc_ref(v_inst_295_);
    v___f_303_ = leanh::lean_alloc_closure(
        l_Std_Queue_filterM___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_303_, 0, v_toPure_302_);
    leanh::lean_closure_set(v___f_303_, 1, v_inst_295_);
    leanh::lean_closure_set(v___f_303_, 2, v_p_296_);
    leanh::lean_closure_set(v___f_303_, 3, v_eList_300_);
    leanh::lean_closure_set(v___f_303_, 4, v_toBind_299_);
    v___x_304_ = leanh::lean_box(0);
    v___x_305_ = l_List_filterAuxM___redArg(v_inst_295_, v_p_296_, v_dList_301_, v___x_304_);
    v___f_306_ = leanh::lean_alloc_closure(
        l_Std_Queue_filterM___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_306_, 0, v_toPure_302_);
    v___x_307_ = leanh::lean_apply_4(
        v_toBind_299_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_305_,
        v___f_306_,
    );
    v___x_308_ = leanh::lean_apply_4(
        v_toBind_299_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_307_,
        v___f_303_,
    );
    return v___x_308_;
}
pub unsafe fn l_Std_Queue_filterM(
    mut v_m_309_: *mut leanh::LeanObject,
    mut v_inst_310_: *mut leanh::LeanObject,
    mut v_00_u03b1_311_: *mut leanh::LeanObject,
    mut v_p_312_: *mut leanh::LeanObject,
    mut v_q_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_314_ = l_Std_Queue_filterM___redArg(v_inst_310_, v_p_312_, v_q_313_);
    return v___x_314_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Queue(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Queue(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Queue(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Queue(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Queue(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Queue(builtin);
}