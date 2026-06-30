// Lean compiler output
// Module: Lean.Elab.InfoTree.InlayHints
// Imports: Lean.Meta.Basic
use crate::ffi::lean_string_dec_eq;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_instBEqRange_beq;
pub static l_Lean_Elab_instBEqInlayHintTextEdit___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_instBEqInlayHintTextEdit_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_instBEqInlayHintTextEdit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqInlayHintTextEdit___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instBEqInlayHintTextEdit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instBEqInlayHintTextEdit___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 108, 97, 121, 72, 105, 110, 116, 0]};
static mut l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__0_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__1_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__2_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject,18025523747594773059 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instImpl_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instTypeNameInlayHint: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_instImpl___closed__3_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_InlayHintLabel_ctorIdx(
    mut v_x_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_164_) == 0 {
        let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_165_ = leanh::lean_unsigned_to_nat(0);
        return v___x_165_;
    } else {
        let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_166_ = leanh::lean_unsigned_to_nat(1);
        return v___x_166_;
    }
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_ctorIdx___boxed(
    mut v_x_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_Lean_Elab_InlayHintLabel_ctorIdx(v_x_167_);
    leanh::lean_dec_ref(v_x_167_);
    return v_res_168_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_ctorElim___redArg(
    mut v_t_169_: *mut leanh::LeanObject,
    mut v_k_170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_171_ = leanh::lean_ctor_get(v_t_169_, 0);
    leanh::lean_inc_ref(v_n_171_);
    leanh::lean_dec_ref(v_t_169_);
    v___x_172_ = leanh::lean_apply_1(v_k_170_, v_n_171_);
    return v___x_172_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_ctorElim(
    mut v_motive_173_: *mut leanh::LeanObject,
    mut v_ctorIdx_174_: *mut leanh::LeanObject,
    mut v_t_175_: *mut leanh::LeanObject,
    mut v_h_176_: *mut leanh::LeanObject,
    mut v_k_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_178_ = l_Lean_Elab_InlayHintLabel_ctorElim___redArg(v_t_175_, v_k_177_);
    return v___x_178_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_ctorElim___boxed(
    mut v_motive_179_: *mut leanh::LeanObject,
    mut v_ctorIdx_180_: *mut leanh::LeanObject,
    mut v_t_181_: *mut leanh::LeanObject,
    mut v_h_182_: *mut leanh::LeanObject,
    mut v_k_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_184_ = l_Lean_Elab_InlayHintLabel_ctorElim(
        v_motive_179_,
        v_ctorIdx_180_,
        v_t_181_,
        v_h_182_,
        v_k_183_,
    );
    leanh::lean_dec(v_ctorIdx_180_);
    return v_res_184_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_name_elim___redArg(
    mut v_t_185_: *mut leanh::LeanObject,
    mut v_name_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_187_ = l_Lean_Elab_InlayHintLabel_ctorElim___redArg(v_t_185_, v_name_186_);
    return v___x_187_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_name_elim(
    mut v_motive_188_: *mut leanh::LeanObject,
    mut v_t_189_: *mut leanh::LeanObject,
    mut v_h_190_: *mut leanh::LeanObject,
    mut v_name_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ = l_Lean_Elab_InlayHintLabel_ctorElim___redArg(v_t_189_, v_name_191_);
    return v___x_192_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_parts_elim___redArg(
    mut v_t_193_: *mut leanh::LeanObject,
    mut v_parts_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_195_ = l_Lean_Elab_InlayHintLabel_ctorElim___redArg(v_t_193_, v_parts_194_);
    return v___x_195_;
}
pub unsafe fn l_Lean_Elab_InlayHintLabel_parts_elim(
    mut v_motive_196_: *mut leanh::LeanObject,
    mut v_t_197_: *mut leanh::LeanObject,
    mut v_h_198_: *mut leanh::LeanObject,
    mut v_parts_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_200_ = l_Lean_Elab_InlayHintLabel_ctorElim___redArg(v_t_197_, v_parts_199_);
    return v___x_200_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_ctorIdx(mut v_x_201_: u8) -> *mut leanh::LeanObject {
    if v_x_201_ == 0 {
        let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_202_ = leanh::lean_unsigned_to_nat(0);
        return v___x_202_;
    } else {
        let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_203_ = leanh::lean_unsigned_to_nat(1);
        return v___x_203_;
    }
}
pub unsafe fn l_Lean_Elab_InlayHintKind_ctorIdx___boxed(
    mut v_x_204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_205_: u8 = 0;
    let mut v_res_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_205_ = (leanh::lean_unbox(v_x_204_) as u8);
    v_res_206_ = l_Lean_Elab_InlayHintKind_ctorIdx(v_x_boxed_205_);
    return v_res_206_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_toCtorIdx(
    mut v_x_207_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = l_Lean_Elab_InlayHintKind_ctorIdx(v_x_207_);
    return v___x_208_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_toCtorIdx___boxed(
    mut v_x_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_210_: u8 = 0;
    let mut v_res_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_210_ = (leanh::lean_unbox(v_x_209_) as u8);
    v_res_211_ = l_Lean_Elab_InlayHintKind_toCtorIdx(v_x_4__boxed_210_);
    return v_res_211_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_ctorElim___redArg(
    mut v_k_212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_212_);
    return v_k_212_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_ctorElim___redArg___boxed(
    mut v_k_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l_Lean_Elab_InlayHintKind_ctorElim___redArg(v_k_213_);
    leanh::lean_dec(v_k_213_);
    return v_res_214_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_ctorElim(
    mut v_motive_215_: *mut leanh::LeanObject,
    mut v_ctorIdx_216_: *mut leanh::LeanObject,
    mut v_t_217_: u8,
    mut v_h_218_: *mut leanh::LeanObject,
    mut v_k_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_219_);
    return v_k_219_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_ctorElim___boxed(
    mut v_motive_220_: *mut leanh::LeanObject,
    mut v_ctorIdx_221_: *mut leanh::LeanObject,
    mut v_t_222_: *mut leanh::LeanObject,
    mut v_h_223_: *mut leanh::LeanObject,
    mut v_k_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_225_: u8 = 0;
    let mut v_res_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_225_ = (leanh::lean_unbox(v_t_222_) as u8);
    v_res_226_ = l_Lean_Elab_InlayHintKind_ctorElim(
        v_motive_220_,
        v_ctorIdx_221_,
        v_t_boxed_225_,
        v_h_223_,
        v_k_224_,
    );
    leanh::lean_dec(v_k_224_);
    leanh::lean_dec(v_ctorIdx_221_);
    return v_res_226_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_type_elim___redArg(
    mut v_type_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_type_227_);
    return v_type_227_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_type_elim___redArg___boxed(
    mut v_type_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Lean_Elab_InlayHintKind_type_elim___redArg(v_type_228_);
    leanh::lean_dec(v_type_228_);
    return v_res_229_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_type_elim(
    mut v_motive_230_: *mut leanh::LeanObject,
    mut v_t_231_: u8,
    mut v_h_232_: *mut leanh::LeanObject,
    mut v_type_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_type_233_);
    return v_type_233_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_type_elim___boxed(
    mut v_motive_234_: *mut leanh::LeanObject,
    mut v_t_235_: *mut leanh::LeanObject,
    mut v_h_236_: *mut leanh::LeanObject,
    mut v_type_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_238_: u8 = 0;
    let mut v_res_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_238_ = (leanh::lean_unbox(v_t_235_) as u8);
    v_res_239_ =
        l_Lean_Elab_InlayHintKind_type_elim(v_motive_234_, v_t_boxed_238_, v_h_236_, v_type_237_);
    leanh::lean_dec(v_type_237_);
    return v_res_239_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_parameter_elim___redArg(
    mut v_parameter_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_parameter_240_);
    return v_parameter_240_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_parameter_elim___redArg___boxed(
    mut v_parameter_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Elab_InlayHintKind_parameter_elim___redArg(v_parameter_241_);
    leanh::lean_dec(v_parameter_241_);
    return v_res_242_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_parameter_elim(
    mut v_motive_243_: *mut leanh::LeanObject,
    mut v_t_244_: u8,
    mut v_h_245_: *mut leanh::LeanObject,
    mut v_parameter_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_parameter_246_);
    return v_parameter_246_;
}
pub unsafe fn l_Lean_Elab_InlayHintKind_parameter_elim___boxed(
    mut v_motive_247_: *mut leanh::LeanObject,
    mut v_t_248_: *mut leanh::LeanObject,
    mut v_h_249_: *mut leanh::LeanObject,
    mut v_parameter_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_251_: u8 = 0;
    let mut v_res_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_251_ = (leanh::lean_unbox(v_t_248_) as u8);
    v_res_252_ = l_Lean_Elab_InlayHintKind_parameter_elim(
        v_motive_247_,
        v_t_boxed_251_,
        v_h_249_,
        v_parameter_250_,
    );
    leanh::lean_dec(v_parameter_250_);
    return v_res_252_;
}
pub unsafe fn l_Lean_Elab_instBEqInlayHintTextEdit_beq(
    mut v_x_253_: *mut leanh::LeanObject,
    mut v_x_254_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_range_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: u8 = 0;
    v_range_255_ = leanh::lean_ctor_get(v_x_253_, 0);
    v_newText_256_ = leanh::lean_ctor_get(v_x_253_, 1);
    v_range_257_ = leanh::lean_ctor_get(v_x_254_, 0);
    v_newText_258_ = leanh::lean_ctor_get(v_x_254_, 1);
    v___x_259_ = l_Lean_Syntax_instBEqRange_beq(v_range_255_, v_range_257_);
    if v___x_259_ == 0 {
        return v___x_259_;
    } else {
        let mut v___x_260_: u8 = 0;
        v___x_260_ = lean_string_dec_eq(v_newText_256_, v_newText_258_);
        return v___x_260_;
    }
}
pub unsafe fn l_Lean_Elab_instBEqInlayHintTextEdit_beq___boxed(
    mut v_x_261_: *mut leanh::LeanObject,
    mut v_x_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_263_: u8 = 0;
    let mut v_r_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_263_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_x_261_, v_x_262_);
    leanh::lean_dec_ref(v_x_262_);
    leanh::lean_dec_ref(v_x_261_);
    v_r_264_ = leanh::lean_box((v_res_263_) as usize);
    return v_r_264_;
}
pub unsafe fn l_Lean_Elab_InlayHint_toCustomInfo(
    mut v_i_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ =
        l_Lean_Elab_instImpl_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_;
    v___x_278_ = leanh::lean_box(0);
    v___x_279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_279_, 0, v___x_277_);
    leanh::lean_ctor_set(v___x_279_, 1, v_i_276_);
    v___x_280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_280_, 0, v___x_278_);
    leanh::lean_ctor_set(v___x_280_, 1, v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_Lean_Elab_InlayHint_ofCustomInfo_x3f(
    mut v_c_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_value_282_ = leanh::lean_ctor_get(v_c_281_, 1);
    v___x_283_ =
        l_Lean_Elab_instImpl_00___x40_Lean_Elab_InfoTree_InlayHints_1870855000____hygCtx___hyg_20_;
    v___x_284_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_282_, v___x_283_);
    return v___x_284_;
}
pub unsafe fn l_Lean_Elab_InlayHint_ofCustomInfo_x3f___boxed(
    mut v_c_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_286_ = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(v_c_285_);
    leanh::lean_dec_ref(v_c_285_);
    return v_res_286_;
}
pub unsafe fn l_Lean_Elab_InlayHint_resolveDeferred(
    mut v_i_287_: *mut leanh::LeanObject,
    mut v_a_288_: *mut leanh::LeanObject,
    mut v_a_289_: *mut leanh::LeanObject,
    mut v_a_290_: *mut leanh::LeanObject,
    mut v_a_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInlayHintInfo_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deferredResolution_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_298_: u8 = 0;
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_303_: u8 = 0;
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_310_: u8 = 0;
    let mut v_a_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_314_: u8 = 0;
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_318_: u8 = 0;
    let mut v_isSharedCheck_319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInlayHintInfo_293_ = leanh::lean_ctor_get(v_i_287_, 0);
                v_lctx_294_ = leanh::lean_ctor_get(v_i_287_, 1);
                v_deferredResolution_295_ = leanh::lean_ctor_get(v_i_287_, 2);
                v_isSharedCheck_319_ = (!leanh::lean_is_exclusive(v_i_287_)) as u8;
                if v_isSharedCheck_319_ == 0 {
                    v___x_297_ = v_i_287_;
                    v_isShared_298_ = v_isSharedCheck_319_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_deferredResolution_295_);
                    leanh::lean_inc(v_lctx_294_);
                    leanh::lean_inc(v_toInlayHintInfo_293_);
                    leanh::lean_dec(v_i_287_);
                    v___x_297_ = leanh::lean_box(0);
                    v_isShared_298_ = v_isSharedCheck_319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_deferredResolution_295_);
                leanh::lean_inc(v_a_291_);
                leanh::lean_inc_ref(v_a_290_);
                leanh::lean_inc(v_a_289_);
                leanh::lean_inc_ref(v_a_288_);
                v___x_299_ = leanh::lean_apply_6(
                    v_deferredResolution_295_,
                    v_toInlayHintInfo_293_,
                    v_a_288_,
                    v_a_289_,
                    v_a_290_,
                    v_a_291_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_299_) == 0 {
                    v_a_300_ = leanh::lean_ctor_get(v___x_299_, 0);
                    v_isSharedCheck_310_ = (!leanh::lean_is_exclusive(v___x_299_)) as u8;
                    if v_isSharedCheck_310_ == 0 {
                        v___x_302_ = v___x_299_;
                        v_isShared_303_ = v_isSharedCheck_310_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_300_);
                        leanh::lean_dec(v___x_299_);
                        v___x_302_ = leanh::lean_box(0);
                        v_isShared_303_ = v_isSharedCheck_310_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_297_);
                    leanh::lean_dec_ref(v_deferredResolution_295_);
                    leanh::lean_dec_ref(v_lctx_294_);
                    v_a_311_ = leanh::lean_ctor_get(v___x_299_, 0);
                    v_isSharedCheck_318_ = (!leanh::lean_is_exclusive(v___x_299_)) as u8;
                    if v_isSharedCheck_318_ == 0 {
                        v___x_313_ = v___x_299_;
                        v_isShared_314_ = v_isSharedCheck_318_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_311_);
                        leanh::lean_dec(v___x_299_);
                        v___x_313_ = leanh::lean_box(0);
                        v_isShared_314_ = v_isSharedCheck_318_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_298_ == 0 {
                    leanh::lean_ctor_set(v___x_297_, 0, v_a_300_);
                    v___x_305_ = v___x_297_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_309_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_309_, 1, v_lctx_294_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_309_,
                        2,
                        v_deferredResolution_295_,
                    );
                    v___x_305_ = v_reuseFailAlloc_309_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_303_ == 0 {
                    leanh::lean_ctor_set(v___x_302_, 0, v___x_305_);
                    v___x_307_ = v___x_302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
                    v___x_307_ = v_reuseFailAlloc_308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_307_;
            }
            5 => {
                if v_isShared_314_ == 0 {
                    v___x_316_ = v___x_313_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
                    v___x_316_ = v_reuseFailAlloc_317_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_InlayHint_resolveDeferred___boxed(
    mut v_i_320_: *mut leanh::LeanObject,
    mut v_a_321_: *mut leanh::LeanObject,
    mut v_a_322_: *mut leanh::LeanObject,
    mut v_a_323_: *mut leanh::LeanObject,
    mut v_a_324_: *mut leanh::LeanObject,
    mut v_a_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ =
        l_Lean_Elab_InlayHint_resolveDeferred(v_i_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
    leanh::lean_dec(v_a_324_);
    leanh::lean_dec_ref(v_a_323_);
    leanh::lean_dec(v_a_322_);
    leanh::lean_dec_ref(v_a_321_);
    return v_res_326_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InfoTree_InlayHints(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InfoTree_InlayHints(
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
pub unsafe fn initialize_Lean_Elab_InfoTree_InlayHints(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_InlayHints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InfoTree_InlayHints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_InfoTree_InlayHints(builtin);
}