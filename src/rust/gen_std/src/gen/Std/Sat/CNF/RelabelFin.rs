// Lean compiler output
// Module: Std.Sat.CNF.RelabelFin
// Imports: Init.Data.Nat.Order Std.Sat.CNF.Relabel Init.Data.Option.Lemmas Init.Omega Init.Data.List.Impl Init.Data.List.MinMax Init.Data.Array.MinMax Init.TacticsExtra
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::MinMax::{
    initialize_Init_Data_Array_MinMax, runtime_initialize_Init_Data_Array_MinMax,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::List::MinMax::{
    initialize_Init_Data_List_MinMax, runtime_initialize_Init_Data_List_MinMax,
};
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::r#gen::Std::Sat::CNF::Basic::l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg;
use crate::r#gen::Std::Sat::CNF::Relabel::{
    initialize_Std_Sat_CNF_Relabel, l_Std_Sat_CNF_relabel___redArg,
    runtime_initialize_Std_Sat_CNF_Relabel,
};
pub static l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(
    mut v_a_172_: *mut leanh::LeanObject,
    mut v_a_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_179_: u8 = 0;
    let mut v_fst_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_172_) == 0 {
                    v___x_174_ = l_List_reverse___redArg(v_a_173_);
                    return v___x_174_;
                } else {
                    v_head_175_ = leanh::lean_ctor_get(v_a_172_, 0);
                    v_tail_176_ = leanh::lean_ctor_get(v_a_172_, 1);
                    v_isSharedCheck_185_ = (!leanh::lean_is_exclusive(v_a_172_)) as u8;
                    if v_isSharedCheck_185_ == 0 {
                        v___x_178_ = v_a_172_;
                        v_isShared_179_ = v_isSharedCheck_185_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_176_);
                        leanh::lean_inc(v_head_175_);
                        leanh::lean_dec(v_a_172_);
                        v___x_178_ = leanh::lean_box(0);
                        v_isShared_179_ = v_isSharedCheck_185_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_180_ = leanh::lean_ctor_get(v_head_175_, 0);
                leanh::lean_inc(v_fst_180_);
                leanh::lean_dec(v_head_175_);
                if v_isShared_179_ == 0 {
                    leanh::lean_ctor_set(v___x_178_, 1, v_a_173_);
                    leanh::lean_ctor_set(v___x_178_, 0, v_fst_180_);
                    v___x_182_ = v___x_178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_184_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_184_, 0, v_fst_180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_184_, 1, v_a_173_);
                    v___x_182_ = v_reuseFailAlloc_184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_172_ = v_tail_176_;
                v_a_173_ = v___x_182_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(
    mut v_x_186_: *mut leanh::LeanObject,
    mut v_x_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_187_) == 0 {
                    leanh::lean_inc(v_x_186_);
                    return v_x_186_;
                } else {
                    v_head_188_ = leanh::lean_ctor_get(v_x_187_, 0);
                    v_tail_189_ = leanh::lean_ctor_get(v_x_187_, 1);
                    v___x_190_ = lean_nat_dec_le(v_x_186_, v_head_188_);
                    if v___x_190_ == 0 {
                        v_x_187_ = v_tail_189_;
                        state = 0;
                        continue;
                    } else {
                        v_x_186_ = v_head_188_;
                        v_x_187_ = v_tail_189_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1___boxed(
    mut v_x_193_: *mut leanh::LeanObject,
    mut v_x_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_195_ =
        l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(
            v_x_193_, v_x_194_,
        );
    leanh::lean_dec(v_x_194_);
    leanh::lean_dec(v_x_193_);
    return v_res_195_;
}
pub unsafe fn l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(
    mut v_x_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_196_) == 0 {
        let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_197_ = leanh::lean_box(0);
        return v___x_197_;
    } else {
        let mut v_head_198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_198_ = leanh::lean_ctor_get(v_x_196_, 0);
        v_tail_199_ = leanh::lean_ctor_get(v_x_196_, 1);
        v___x_200_ = l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(v_head_198_, v_tail_199_);
        v___x_201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_201_, 0, v___x_200_);
        return v___x_201_;
    }
}
pub unsafe fn l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1___boxed(
    mut v_x_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_203_ = l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(v_x_202_);
    leanh::lean_dec(v_x_202_);
    return v_res_203_;
}
pub unsafe fn l_Std_Sat_CNF_Clause_maxLiteral(
    mut v_c_204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_205_ = leanh::lean_box(0);
    v___x_206_ =
        l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v_c_204_, v___x_205_);
    v___x_207_ = l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(v___x_206_);
    leanh::lean_dec(v___x_206_);
    return v___x_207_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(
    mut v_as_208_: *mut leanh::LeanObject,
    mut v_i_209_: usize,
    mut v_stop_210_: usize,
    mut v_b_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: usize = 0;
    let mut v___x_215_: usize = 0;
    let mut v___x_217_: u8 = 0;
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_217_ = lean_usize_dec_eq(v_i_209_, v_stop_210_);
                if v___x_217_ == 0 {
                    v___x_218_ = lean_array_uget_borrowed(v_as_208_, v_i_209_);
                    leanh::lean_inc(v___x_218_);
                    v___x_219_ = l_Std_Sat_CNF_Clause_maxLiteral(v___x_218_);
                    if leanh::lean_obj_tag(v___x_219_) == 0 {
                        v___y_213_ = v_b_211_;
                        state = 1;
                        continue;
                    } else {
                        v_val_220_ = leanh::lean_ctor_get(v___x_219_, 0);
                        leanh::lean_inc(v_val_220_);
                        leanh::lean_dec_ref_known(v___x_219_, 1);
                        v___x_221_ = lean_array_push(v_b_211_, v_val_220_);
                        v___y_213_ = v___x_221_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_211_;
                }
            }
            1 => {
                v___x_214_ = 1usize;
                v___x_215_ = lean_usize_add(v_i_209_, v___x_214_);
                v_i_209_ = v___x_215_;
                v_b_211_ = v___y_213_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(
    mut v_as_222_: *mut leanh::LeanObject,
    mut v_i_223_: *mut leanh::LeanObject,
    mut v_stop_224_: *mut leanh::LeanObject,
    mut v_b_225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_226_: usize = 0;
    let mut v_stop_boxed_227_: usize = 0;
    let mut v_res_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_226_ = leanh::lean_unbox_usize(v_i_223_);
    leanh::lean_dec(v_i_223_);
    v_stop_boxed_227_ = leanh::lean_unbox_usize(v_stop_224_);
    leanh::lean_dec(v_stop_224_);
    v_res_228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_222_, v_i_boxed_226_, v_stop_boxed_227_, v_b_225_);
    leanh::lean_dec_ref(v_as_222_);
    return v_res_228_;
}
pub unsafe fn l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(
    mut v_as_231_: *mut leanh::LeanObject,
    mut v_start_232_: *mut leanh::LeanObject,
    mut v_stop_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: u8 = 0;
    v___x_234_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0;
    v___x_235_ = lean_nat_dec_lt(v_start_232_, v_stop_233_);
    if v___x_235_ == 0 {
        return v___x_234_;
    } else {
        let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        v___x_236_ = lean_array_get_size(v_as_231_);
        v___x_237_ = lean_nat_dec_le(v_stop_233_, v___x_236_);
        if v___x_237_ == 0 {
            let mut v___x_238_: u8 = 0;
            v___x_238_ = lean_nat_dec_lt(v_start_232_, v___x_236_);
            if v___x_238_ == 0 {
                return v___x_234_;
            } else {
                let mut v___x_239_: usize = 0;
                let mut v___x_240_: usize = 0;
                let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_239_ = lean_usize_of_nat(v_start_232_);
                v___x_240_ = lean_usize_of_nat(v___x_236_);
                v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_231_, v___x_239_, v___x_240_, v___x_234_);
                return v___x_241_;
            }
        } else {
            let mut v___x_242_: usize = 0;
            let mut v___x_243_: usize = 0;
            let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_242_ = lean_usize_of_nat(v_start_232_);
            v___x_243_ = lean_usize_of_nat(v_stop_233_);
            v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_231_, v___x_242_, v___x_243_, v___x_234_);
            return v___x_244_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(
    mut v_as_245_: *mut leanh::LeanObject,
    mut v_start_246_: *mut leanh::LeanObject,
    mut v_stop_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_248_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(
        v_as_245_,
        v_start_246_,
        v_stop_247_,
    );
    leanh::lean_dec(v_stop_247_);
    leanh::lean_dec(v_start_246_);
    leanh::lean_dec_ref(v_as_245_);
    return v_res_248_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(
    mut v_as_249_: *mut leanh::LeanObject,
    mut v_i_250_: usize,
    mut v_stop_251_: usize,
    mut v_b_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: usize = 0;
    let mut v___x_256_: usize = 0;
    let mut v___x_258_: u8 = 0;
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_258_ = lean_usize_dec_eq(v_i_250_, v_stop_251_);
                if v___x_258_ == 0 {
                    v___x_259_ = lean_array_uget_borrowed(v_as_249_, v_i_250_);
                    v___x_260_ = lean_nat_dec_le(v_b_252_, v___x_259_);
                    if v___x_260_ == 0 {
                        v___y_254_ = v_b_252_;
                        state = 1;
                        continue;
                    } else {
                        v___y_254_ = v___x_259_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_b_252_);
                    return v_b_252_;
                }
            }
            1 => {
                v___x_255_ = 1usize;
                v___x_256_ = lean_usize_add(v_i_250_, v___x_255_);
                v_i_250_ = v___x_256_;
                v_b_252_ = v___y_254_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3___boxed(
    mut v_as_261_: *mut leanh::LeanObject,
    mut v_i_262_: *mut leanh::LeanObject,
    mut v_stop_263_: *mut leanh::LeanObject,
    mut v_b_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_265_: usize = 0;
    let mut v_stop_boxed_266_: usize = 0;
    let mut v_res_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_265_ = leanh::lean_unbox_usize(v_i_262_);
    leanh::lean_dec(v_i_262_);
    v_stop_boxed_266_ = leanh::lean_unbox_usize(v_stop_263_);
    leanh::lean_dec(v_stop_263_);
    v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_as_261_, v_i_boxed_265_, v_stop_boxed_266_, v_b_264_);
    leanh::lean_dec(v_b_264_);
    leanh::lean_dec_ref(v_as_261_);
    return v_res_267_;
}
pub unsafe fn l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(
    mut v_arr_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: u8 = 0;
    v___x_269_ = leanh::lean_unsigned_to_nat(0);
    v___x_270_ = lean_array_fget_borrowed(v_arr_268_, v___x_269_);
    v___x_271_ = leanh::lean_unsigned_to_nat(1);
    v___x_272_ = lean_array_get_size(v_arr_268_);
    v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
    if v___x_273_ == 0 {
        leanh::lean_inc(v___x_270_);
        return v___x_270_;
    } else {
        let mut v___x_274_: u8 = 0;
        v___x_274_ = lean_nat_dec_le(v___x_272_, v___x_272_);
        if v___x_274_ == 0 {
            if v___x_273_ == 0 {
                leanh::lean_inc(v___x_270_);
                return v___x_270_;
            } else {
                let mut v___x_275_: usize = 0;
                let mut v___x_276_: usize = 0;
                let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_275_ = 1usize;
                v___x_276_ = lean_usize_of_nat(v___x_272_);
                v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_arr_268_, v___x_275_, v___x_276_, v___x_270_);
                return v___x_277_;
            }
        } else {
            let mut v___x_278_: usize = 0;
            let mut v___x_279_: usize = 0;
            let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_278_ = 1usize;
            v___x_279_ = lean_usize_of_nat(v___x_272_);
            v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(v_arr_268_, v___x_278_, v___x_279_, v___x_270_);
            return v___x_280_;
        }
    }
}
pub unsafe fn l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg___boxed(
    mut v_arr_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_282_ =
        l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(
            v_arr_281_,
        );
    leanh::lean_dec_ref(v_arr_281_);
    return v_res_282_;
}
pub unsafe fn l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(
    mut v_arr_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u8 = 0;
    v___x_284_ = lean_array_get_size(v_arr_283_);
    v___x_285_ = leanh::lean_unsigned_to_nat(0);
    v___x_286_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
    if v___x_286_ == 0 {
        let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_287_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(v_arr_283_);
        v___x_288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_288_, 0, v___x_287_);
        return v___x_288_;
    } else {
        let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_289_ = leanh::lean_box(0);
        return v___x_289_;
    }
}
pub unsafe fn l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1___boxed(
    mut v_arr_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(v_arr_290_);
    leanh::lean_dec_ref(v_arr_290_);
    return v_res_291_;
}
pub unsafe fn l_Std_Sat_CNF_maxLiteral(
    mut v_f_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = leanh::lean_unsigned_to_nat(0);
    v___x_294_ = lean_array_get_size(v_f_292_);
    v___x_295_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(
        v_f_292_, v___x_293_, v___x_294_,
    );
    v___x_296_ = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(v___x_295_);
    leanh::lean_dec_ref(v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_Std_Sat_CNF_maxLiteral___boxed(
    mut v_f_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Std_Sat_CNF_maxLiteral(v_f_297_);
    leanh::lean_dec_ref(v_f_297_);
    return v_res_298_;
}
pub unsafe fn l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(
    mut v_arr_299_: *mut leanh::LeanObject,
    mut v_h_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ =
        l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(
            v_arr_299_,
        );
    return v___x_301_;
}
pub unsafe fn l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___boxed(
    mut v_arr_302_: *mut leanh::LeanObject,
    mut v_h_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(
        v_arr_302_, v_h_303_,
    );
    leanh::lean_dec_ref(v_arr_302_);
    return v_res_304_;
}
pub unsafe fn l_Std_Sat_CNF_numLiterals(
    mut v_f_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_306_ = l_Std_Sat_CNF_maxLiteral(v_f_305_);
    if leanh::lean_obj_tag(v___x_306_) == 0 {
        let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_307_ = leanh::lean_unsigned_to_nat(0);
        return v___x_307_;
    } else {
        let mut v_val_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_308_ = leanh::lean_ctor_get(v___x_306_, 0);
        leanh::lean_inc(v_val_308_);
        leanh::lean_dec_ref_known(v___x_306_, 1);
        v___x_309_ = leanh::lean_unsigned_to_nat(1);
        v___x_310_ = lean_nat_add(v_val_308_, v___x_309_);
        leanh::lean_dec(v_val_308_);
        return v___x_310_;
    }
}
pub unsafe fn l_Std_Sat_CNF_numLiterals___boxed(
    mut v_f_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_Sat_CNF_numLiterals(v_f_311_);
    leanh::lean_dec_ref(v_f_311_);
    return v_res_312_;
}
pub unsafe fn l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(
    mut v_x_313_: *mut leanh::LeanObject,
    mut v_h__1_314_: *mut leanh::LeanObject,
    mut v_h__2_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_313_) == 0 {
        let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_315_);
        v___x_316_ = leanh::lean_box(0);
        v___x_317_ = leanh::lean_apply_1(v_h__1_314_, v___x_316_);
        return v___x_317_;
    } else {
        let mut v_val_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_314_);
        v_val_318_ = leanh::lean_ctor_get(v_x_313_, 0);
        leanh::lean_inc(v_val_318_);
        leanh::lean_dec_ref_known(v_x_313_, 1);
        v___x_319_ = leanh::lean_apply_1(v_h__2_315_, v_val_318_);
        return v___x_319_;
    }
}
pub unsafe fn l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(
    mut v_motive_320_: *mut leanh::LeanObject,
    mut v_x_321_: *mut leanh::LeanObject,
    mut v_h__1_322_: *mut leanh::LeanObject,
    mut v_h__2_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_321_) == 0 {
        let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_323_);
        v___x_324_ = leanh::lean_box(0);
        v___x_325_ = leanh::lean_apply_1(v_h__1_322_, v___x_324_);
        return v___x_325_;
    } else {
        let mut v_val_326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_322_);
        v_val_326_ = leanh::lean_ctor_get(v_x_321_, 0);
        leanh::lean_inc(v_val_326_);
        leanh::lean_dec_ref_known(v_x_321_, 1);
        v___x_327_ = leanh::lean_apply_1(v_h__2_323_, v_val_326_);
        return v___x_327_;
    }
}
pub unsafe fn l_Std_Sat_CNF_relabelFin___lam__0(
    mut v_n_328_: *mut leanh::LeanObject,
    mut v_i_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_330_: u8 = 0;
    v___x_330_ = lean_nat_dec_lt(v_i_329_, v_n_328_);
    if v___x_330_ == 0 {
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_331_ = leanh::lean_unsigned_to_nat(0);
        return v___x_331_;
    } else {
        leanh::lean_inc(v_i_329_);
        return v_i_329_;
    }
}
pub unsafe fn l_Std_Sat_CNF_relabelFin___lam__0___boxed(
    mut v_n_332_: *mut leanh::LeanObject,
    mut v_i_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l_Std_Sat_CNF_relabelFin___lam__0(v_n_332_, v_i_333_);
    leanh::lean_dec(v_i_333_);
    leanh::lean_dec(v_n_332_);
    return v_res_334_;
}
pub unsafe fn l_Std_Sat_CNF_relabelFin(
    mut v_f_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_336_: u8 = 0;
    leanh::lean_inc_ref(v_f_335_);
    v___x_336_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_335_);
    if v___x_336_ == 0 {
        let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_337_ = lean_array_get_size(v_f_335_);
        leanh::lean_dec_ref(v_f_335_);
        v___x_338_ = leanh::lean_box(0);
        v___x_339_ = lean_mk_array(v___x_337_, v___x_338_);
        return v___x_339_;
    } else {
        let mut v_n_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_340_ = l_Std_Sat_CNF_numLiterals(v_f_335_);
        v___f_341_ = leanh::lean_alloc_closure(
            l_Std_Sat_CNF_relabelFin___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_341_, 0, v_n_340_);
        v___x_342_ = l_Std_Sat_CNF_relabel___redArg(v___f_341_, v_f_335_);
        return v___x_342_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_CNF_RelabelFin(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MinMax(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_CNF_RelabelFin(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_CNF_RelabelFin(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_CNF_Relabel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_CNF_RelabelFin(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_CNF_RelabelFin(builtin);
}