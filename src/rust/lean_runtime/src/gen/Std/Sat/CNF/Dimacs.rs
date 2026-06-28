// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: Std.Sat.CNF.RelabelFin
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Std::Sat::CNF::RelabelFin::{
    initialize_Std_Sat_CNF_RelabelFin, runtime_initialize_Std_Sat_CNF_RelabelFin,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Sat_CNF_dimacs___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Sat_CNF_dimacs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_CNF_dimacs___closed__0_value) as *mut LeanObject;
pub static l_Std_Sat_CNF_dimacs___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [112, 32, 99, 110, 102, 32, 0],
};
static mut l_Std_Sat_CNF_dimacs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_CNF_dimacs___closed__1_value) as *mut LeanObject;
pub static l_Std_Sat_CNF_dimacs___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Std_Sat_CNF_dimacs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_CNF_dimacs___closed__2_value) as *mut LeanObject;
pub static l_Std_Sat_CNF_dimacs___closed__3_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Std_Sat_CNF_dimacs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Sat_CNF_dimacs___closed__3_value) as *mut LeanObject;
pub unsafe fn l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(
    mut v_lit_167_: *mut LeanObject,
    mut v_a_168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numClauses_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxLit_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_174_: u8 = 0;
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: u8 = 0;
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_182_: u8 = 0;
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_189_: u8 = 0;
    let mut v_unused_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_192_: u8 = 0;
    let mut v_unused_193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numClauses_169_ = lean_ctor_get(v_a_168_, 0);
                v_maxLit_170_ = lean_ctor_get(v_a_168_, 1);
                v_fst_171_ = lean_ctor_get(v_lit_167_, 0);
                v_isSharedCheck_192_ = (!lean_is_exclusive(v_lit_167_)) as u8;
                if v_isSharedCheck_192_ == 0 {
                    v_unused_193_ = lean_ctor_get(v_lit_167_, 1);
                    lean_dec(v_unused_193_);
                    v___x_173_ = v_lit_167_;
                    v_isShared_174_ = v_isSharedCheck_192_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fst_171_);
                    lean_dec(v_lit_167_);
                    v___x_173_ = lean_box(0);
                    v_isShared_174_ = v_isSharedCheck_192_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_175_ = lean_box(0);
                v___x_176_ = lean_nat_dec_le(v_maxLit_170_, v_fst_171_);
                if v___x_176_ == 0 {
                    lean_dec(v_fst_171_);
                    if v_isShared_174_ == 0 {
                        lean_ctor_set(v___x_173_, 1, v_a_168_);
                        lean_ctor_set(v___x_173_, 0, v___x_175_);
                        v___x_178_ = v___x_173_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_175_);
                        lean_ctor_set(v_reuseFailAlloc_179_, 1, v_a_168_);
                        v___x_178_ = v_reuseFailAlloc_179_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_numClauses_169_);
                    v_isSharedCheck_189_ = (!lean_is_exclusive(v_a_168_)) as u8;
                    if v_isSharedCheck_189_ == 0 {
                        v_unused_190_ = lean_ctor_get(v_a_168_, 1);
                        lean_dec(v_unused_190_);
                        v_unused_191_ = lean_ctor_get(v_a_168_, 0);
                        lean_dec(v_unused_191_);
                        v___x_181_ = v_a_168_;
                        v_isShared_182_ = v_isSharedCheck_189_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_a_168_);
                        v___x_181_ = lean_box(0);
                        v_isShared_182_ = v_isSharedCheck_189_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_178_;
            }
            3 => {
                if v_isShared_182_ == 0 {
                    lean_ctor_set(v___x_181_, 1, v_fst_171_);
                    v___x_184_ = v___x_181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_188_, 0, v_numClauses_169_);
                    lean_ctor_set(v_reuseFailAlloc_188_, 1, v_fst_171_);
                    v___x_184_ = v_reuseFailAlloc_188_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_174_ == 0 {
                    lean_ctor_set(v___x_173_, 1, v___x_184_);
                    lean_ctor_set(v___x_173_, 0, v___x_175_);
                    v___x_186_ = v___x_173_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_175_);
                    lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
                    v___x_186_ = v_reuseFailAlloc_187_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(
    mut v_a_194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numClauses_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxLit_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_199_: u8 = 0;
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numClauses_195_ = lean_ctor_get(v_a_194_, 0);
                v_maxLit_196_ = lean_ctor_get(v_a_194_, 1);
                v_isSharedCheck_207_ = (!lean_is_exclusive(v_a_194_)) as u8;
                if v_isSharedCheck_207_ == 0 {
                    v___x_198_ = v_a_194_;
                    v_isShared_199_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_maxLit_196_);
                    lean_inc(v_numClauses_195_);
                    lean_dec(v_a_194_);
                    v___x_198_ = lean_box(0);
                    v_isShared_199_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_200_ = lean_box(0);
                v___x_201_ = lean_unsigned_to_nat(1);
                v___x_202_ = lean_nat_add(v_numClauses_195_, v___x_201_);
                lean_dec(v_numClauses_195_);
                if v_isShared_199_ == 0 {
                    lean_ctor_set(v___x_198_, 0, v___x_202_);
                    v___x_204_ = v___x_198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
                    lean_ctor_set(v_reuseFailAlloc_206_, 1, v_maxLit_196_);
                    v___x_204_ = v_reuseFailAlloc_206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_205_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_205_, 0, v___x_200_);
                lean_ctor_set(v___x_205_, 1, v___x_204_);
                return v___x_205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(
    mut v_x_209_: *mut LeanObject,
    mut v_x_210_: *mut LeanObject,
    mut v___y_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u32 = 0;
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numClauses_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxLit_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: u8 = 0;
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: u8 = 0;
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_244_: u8 = 0;
    let mut v_unused_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_246_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_210_) == 0 {
                    v___x_212_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_212_, 0, v_x_209_);
                    lean_ctor_set(v___x_212_, 1, v___y_211_);
                    return v___x_212_;
                } else {
                    v_head_213_ = lean_ctor_get(v_x_210_, 0);
                    v_tail_214_ = lean_ctor_get(v_x_210_, 1);
                    v_numClauses_222_ = lean_ctor_get(v___y_211_, 0);
                    v_maxLit_223_ = lean_ctor_get(v___y_211_, 1);
                    v_fst_224_ = lean_ctor_get(v_head_213_, 0);
                    v_snd_225_ = lean_ctor_get(v_head_213_, 1);
                    v___x_237_ = lean_nat_dec_le(v_maxLit_223_, v_fst_224_);
                    if v___x_237_ == 0 {
                        v_snd_227_ = v___y_211_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_numClauses_222_);
                        v_isSharedCheck_244_ = (!lean_is_exclusive(v___y_211_)) as u8;
                        if v_isSharedCheck_244_ == 0 {
                            v_unused_245_ = lean_ctor_get(v___y_211_, 1);
                            lean_dec(v_unused_245_);
                            v_unused_246_ = lean_ctor_get(v___y_211_, 0);
                            lean_dec(v_unused_246_);
                            v___x_239_ = v___y_211_;
                            v_isShared_240_ = v_isSharedCheck_244_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___y_211_);
                            v___x_239_ = lean_box(0);
                            v_isShared_240_ = v_isSharedCheck_244_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_218_ = lean_string_append(v_x_209_, v___y_217_);
                lean_dec_ref(v___y_217_);
                v___x_219_ = 32;
                v___x_220_ = lean_string_push(v___x_218_, v___x_219_);
                v_x_209_ = v___x_220_;
                v_x_210_ = v_tail_214_;
                v___y_211_ = v___y_216_;
                state = 0;
                continue;
            }
            2 => {
                v___x_228_ = (lean_unbox(v_snd_225_) as u8);
                if v___x_228_ == 0 {
                    v___x_229_ = l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0;
                    v___x_230_ = lean_unsigned_to_nat(1);
                    v___x_231_ = lean_nat_add(v_fst_224_, v___x_230_);
                    v___x_232_ = l_Nat_reprFast(v___x_231_);
                    v___x_233_ = lean_string_append(v___x_229_, v___x_232_);
                    lean_dec_ref(v___x_232_);
                    v___y_216_ = v_snd_227_;
                    v___y_217_ = v___x_233_;
                    state = 1;
                    continue;
                } else {
                    v___x_234_ = lean_unsigned_to_nat(1);
                    v___x_235_ = lean_nat_add(v_fst_224_, v___x_234_);
                    v___x_236_ = l_Nat_reprFast(v___x_235_);
                    v___y_216_ = v_snd_227_;
                    v___y_217_ = v___x_236_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc(v_fst_224_);
                if v_isShared_240_ == 0 {
                    lean_ctor_set(v___x_239_, 1, v_fst_224_);
                    v___x_242_ = v___x_239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_243_, 0, v_numClauses_222_);
                    lean_ctor_set(v_reuseFailAlloc_243_, 1, v_fst_224_);
                    v___x_242_ = v_reuseFailAlloc_243_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_snd_227_ = v___x_242_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___boxed(
    mut v_x_247_: *mut LeanObject,
    mut v_x_248_: *mut LeanObject,
    mut v___y_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_250_: *mut LeanObject = core::ptr::null_mut();
    v_res_250_ =
        l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(
            v_x_247_, v_x_248_, v___y_249_,
        );
    lean_dec(v_x_248_);
    return v_res_250_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(
    mut v_as_251_: *mut LeanObject,
    mut v_i_252_: usize,
    mut v_stop_253_: usize,
    mut v_b_254_: *mut LeanObject,
    mut v___y_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_256_: u8 = 0;
    let mut v_numClauses_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxLit_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_261_: u8 = 0;
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: u32 = 0;
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: u32 = 0;
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: usize = 0;
    let mut v___x_275_: usize = 0;
    let mut v_reuseFailAlloc_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_278_: u8 = 0;
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_256_ = lean_usize_dec_eq(v_i_252_, v_stop_253_);
                if v___x_256_ == 0 {
                    v_numClauses_257_ = lean_ctor_get(v___y_255_, 0);
                    v_maxLit_258_ = lean_ctor_get(v___y_255_, 1);
                    v_isSharedCheck_278_ = (!lean_is_exclusive(v___y_255_)) as u8;
                    if v_isSharedCheck_278_ == 0 {
                        v___x_260_ = v___y_255_;
                        v_isShared_261_ = v_isSharedCheck_278_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_maxLit_258_);
                        lean_inc(v_numClauses_257_);
                        lean_dec(v___y_255_);
                        v___x_260_ = lean_box(0);
                        v_isShared_261_ = v_isSharedCheck_278_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_279_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_279_, 0, v_b_254_);
                    lean_ctor_set(v___x_279_, 1, v___y_255_);
                    return v___x_279_;
                }
            }
            1 => {
                v___x_262_ = lean_array_uget_borrowed(v_as_251_, v_i_252_);
                v___x_263_ = lean_unsigned_to_nat(1);
                v___x_264_ = lean_nat_add(v_numClauses_257_, v___x_263_);
                lean_dec(v_numClauses_257_);
                if v_isShared_261_ == 0 {
                    lean_ctor_set(v___x_260_, 0, v___x_264_);
                    v___x_266_ = v___x_260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_264_);
                    lean_ctor_set(v_reuseFailAlloc_277_, 1, v_maxLit_258_);
                    v___x_266_ = v_reuseFailAlloc_277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_267_ = l_List_foldlM___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(v_b_254_, v___x_262_, v___x_266_);
                v_fst_268_ = lean_ctor_get(v___x_267_, 0);
                lean_inc(v_fst_268_);
                v_snd_269_ = lean_ctor_get(v___x_267_, 1);
                lean_inc(v_snd_269_);
                lean_dec_ref(v___x_267_);
                v___x_270_ = 48;
                v___x_271_ = lean_string_push(v_fst_268_, v___x_270_);
                v___x_272_ = 10;
                v___x_273_ = lean_string_push(v___x_271_, v___x_272_);
                v___x_274_ = 1usize;
                v___x_275_ = lean_usize_add(v_i_252_, v___x_274_);
                v_i_252_ = v___x_275_;
                v_b_254_ = v___x_273_;
                v___y_255_ = v_snd_269_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1___boxed(
    mut v_as_280_: *mut LeanObject,
    mut v_i_281_: *mut LeanObject,
    mut v_stop_282_: *mut LeanObject,
    mut v_b_283_: *mut LeanObject,
    mut v___y_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_285_: usize = 0;
    let mut v_stop_boxed_286_: usize = 0;
    let mut v_res_287_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_285_ = lean_unbox_usize(v_i_281_);
    lean_dec(v_i_281_);
    v_stop_boxed_286_ = lean_unbox_usize(v_stop_282_);
    lean_dec(v_stop_282_);
    v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_as_280_, v_i_boxed_285_, v_stop_boxed_286_, v_b_283_, v___y_284_);
    lean_dec_ref(v_as_280_);
    return v_res_287_;
}
pub unsafe fn l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(
    mut v_cnf_289_: *mut LeanObject,
    mut v_a_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: u8 = 0;
    v___x_291_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0;
    v___x_292_ = lean_unsigned_to_nat(0);
    v___x_293_ = lean_array_get_size(v_cnf_289_);
    v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
    if v___x_294_ == 0 {
        let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
        v___x_295_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_295_, 0, v___x_291_);
        lean_ctor_set(v___x_295_, 1, v_a_290_);
        return v___x_295_;
    } else {
        let mut v___x_296_: u8 = 0;
        v___x_296_ = lean_nat_dec_le(v___x_293_, v___x_293_);
        if v___x_296_ == 0 {
            if v___x_294_ == 0 {
                let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
                v___x_297_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_297_, 0, v___x_291_);
                lean_ctor_set(v___x_297_, 1, v_a_290_);
                return v___x_297_;
            } else {
                let mut v___x_298_: usize = 0;
                let mut v___x_299_: usize = 0;
                let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
                v___x_298_ = 0usize;
                v___x_299_ = lean_usize_of_nat(v___x_293_);
                v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_cnf_289_, v___x_298_, v___x_299_, v___x_291_, v_a_290_);
                return v___x_300_;
            }
        } else {
            let mut v___x_301_: usize = 0;
            let mut v___x_302_: usize = 0;
            let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
            v___x_301_ = 0usize;
            v___x_302_ = lean_usize_of_nat(v___x_293_);
            v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_cnf_289_, v___x_301_, v___x_302_, v___x_291_, v_a_290_);
            return v___x_303_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___boxed(
    mut v_cnf_304_: *mut LeanObject,
    mut v_a_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_306_: *mut LeanObject = core::ptr::null_mut();
    v_res_306_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(v_cnf_304_, v_a_305_);
    lean_dec_ref(v_cnf_304_);
    return v_res_306_;
}
pub unsafe fn l_Std_Sat_CNF_dimacs(mut v_cnf_312_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numClauses_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxLit_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v___x_313_ = l_Std_Sat_CNF_dimacs___closed__0;
    v___x_314_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(v_cnf_312_, v___x_313_);
    v_snd_315_ = lean_ctor_get(v___x_314_, 1);
    lean_inc(v_snd_315_);
    v_fst_316_ = lean_ctor_get(v___x_314_, 0);
    lean_inc(v_fst_316_);
    lean_dec_ref(v___x_314_);
    v_numClauses_317_ = lean_ctor_get(v_snd_315_, 0);
    lean_inc(v_numClauses_317_);
    v_maxLit_318_ = lean_ctor_get(v_snd_315_, 1);
    lean_inc(v_maxLit_318_);
    lean_dec(v_snd_315_);
    v___x_319_ = l_Std_Sat_CNF_dimacs___closed__1;
    v___x_320_ = lean_unsigned_to_nat(1);
    v___x_321_ = lean_nat_add(v_maxLit_318_, v___x_320_);
    lean_dec(v_maxLit_318_);
    v___x_322_ = l_Nat_reprFast(v___x_321_);
    v___x_323_ = lean_string_append(v___x_319_, v___x_322_);
    lean_dec_ref(v___x_322_);
    v___x_324_ = l_Std_Sat_CNF_dimacs___closed__2;
    v___x_325_ = lean_string_append(v___x_323_, v___x_324_);
    v___x_326_ = l_Nat_reprFast(v_numClauses_317_);
    v___x_327_ = lean_string_append(v___x_325_, v___x_326_);
    lean_dec_ref(v___x_326_);
    v___x_328_ = l_Std_Sat_CNF_dimacs___closed__3;
    v___x_329_ = lean_string_append(v___x_327_, v___x_328_);
    v___x_330_ = lean_string_append(v___x_329_, v_fst_316_);
    lean_dec(v_fst_316_);
    return v___x_330_;
}
pub unsafe fn l_Std_Sat_CNF_dimacs___boxed(mut v_cnf_331_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_332_: *mut LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Std_Sat_CNF_dimacs(v_cnf_331_);
    lean_dec_ref(v_cnf_331_);
    return v_res_332_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_CNF_Dimacs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_CNF_Dimacs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_CNF_Dimacs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_CNF_RelabelFin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Dimacs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_CNF_Dimacs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_CNF_Dimacs(builtin);
}
