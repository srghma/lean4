// Lean compiler output
// Module: Init.Data.String.Subslice
// Imports: Init.Data.String.Basic Init.Data.String.Lemmas.IsEmpty Init.Data.String.Lemmas.Basic
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_le, lean_nat_sub, lean_panic_fn_borrowed,
};
pub static l_String_Slice_subslice_x21___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 83, 117,
            98, 115, 108, 105, 99, 101, 0,
        ],
    };
static mut l_String_Slice_subslice_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_subslice_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_subslice_x21___closed__1_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 115, 117, 98, 115, 108,
            105, 99, 101, 33, 0,
        ],
    };
static mut l_String_Slice_subslice_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_subslice_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_subslice_x21___closed__2_value: crate::leanh::LeanStringObject<42> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            84, 114, 121, 105, 110, 103, 32, 116, 111, 32, 99, 111, 110, 115, 116, 114, 117, 99,
            116, 32, 97, 32, 100, 101, 103, 101, 110, 101, 114, 97, 116, 101, 32, 115, 117, 98,
            115, 108, 105, 99, 101, 0,
        ],
    };
static mut l_String_Slice_subslice_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_subslice_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_subslice_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_subslice_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_String_Slice_instInhabitedSubslice(
    mut v_s_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_204_ = crate::leanh::lean_ctor_get(v_s_203_, 1);
    v_endExclusive_205_ = crate::leanh::lean_ctor_get(v_s_203_, 2);
    v___x_206_ = lean_nat_sub(v_endExclusive_205_, v_startInclusive_204_);
    crate::leanh::lean_inc(v___x_206_);
    v___x_207_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_207_, 0, v___x_206_);
    crate::leanh::lean_ctor_set(v___x_207_, 1, v___x_206_);
    return v___x_207_;
}
pub unsafe fn l_String_Slice_instInhabitedSubslice___boxed(
    mut v_s_208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_209_ = l_String_Slice_instInhabitedSubslice(v_s_208_);
    crate::leanh::lean_dec_ref(v_s_208_);
    return v_res_209_;
}
pub unsafe fn l_String_Slice_Subslice_toSlice(
    mut v_s_210_: *mut crate::leanh::LeanObject,
    mut v_sl_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_218_: u8 = 0;
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_224_: u8 = 0;
    let mut v_unused_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_212_ = crate::leanh::lean_ctor_get(v_sl_211_, 0);
                v_endExclusive_213_ = crate::leanh::lean_ctor_get(v_sl_211_, 1);
                v_str_214_ = crate::leanh::lean_ctor_get(v_s_210_, 0);
                v_startInclusive_215_ = crate::leanh::lean_ctor_get(v_s_210_, 1);
                v_isSharedCheck_224_ = (!crate::leanh::lean_is_exclusive(v_s_210_)) as u8;
                if v_isSharedCheck_224_ == 0 {
                    v_unused_225_ = crate::leanh::lean_ctor_get(v_s_210_, 2);
                    crate::leanh::lean_dec(v_unused_225_);
                    v___x_217_ = v_s_210_;
                    v_isShared_218_ = v_isSharedCheck_224_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startInclusive_215_);
                    crate::leanh::lean_inc(v_str_214_);
                    crate::leanh::lean_dec(v_s_210_);
                    v___x_217_ = crate::leanh::lean_box(0);
                    v_isShared_218_ = v_isSharedCheck_224_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_219_ = lean_nat_add(v_startInclusive_215_, v_startInclusive_212_);
                v___x_220_ = lean_nat_add(v_startInclusive_215_, v_endExclusive_213_);
                crate::leanh::lean_dec(v_startInclusive_215_);
                if v_isShared_218_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_217_, 2, v___x_220_);
                    crate::leanh::lean_ctor_set(v___x_217_, 1, v___x_219_);
                    v___x_222_ = v___x_217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_223_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_223_, 0, v_str_214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_223_, 1, v___x_219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_223_, 2, v___x_220_);
                    v___x_222_ = v_reuseFailAlloc_223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_toSlice___boxed(
    mut v_s_226_: *mut crate::leanh::LeanObject,
    mut v_sl_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_228_ = l_String_Slice_Subslice_toSlice(v_s_226_, v_sl_227_);
    crate::leanh::lean_dec_ref(v_sl_227_);
    return v_res_228_;
}
pub unsafe fn l_String_Slice_Subslice_instCoeOut(
    mut v_s_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_230_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Subslice_toSlice___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_230_, 0, v_s_229_);
    return v___x_230_;
}
pub unsafe fn l_String_Slice_Subslice_copy(
    mut v_s_231_: *mut crate::leanh::LeanObject,
    mut v_sl_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_233_ = crate::leanh::lean_ctor_get(v_sl_232_, 0);
    v_endExclusive_234_ = crate::leanh::lean_ctor_get(v_sl_232_, 1);
    v_str_235_ = crate::leanh::lean_ctor_get(v_s_231_, 0);
    v_startInclusive_236_ = crate::leanh::lean_ctor_get(v_s_231_, 1);
    v___x_237_ = lean_nat_add(v_startInclusive_236_, v_startInclusive_233_);
    v___x_238_ = lean_nat_add(v_startInclusive_236_, v_endExclusive_234_);
    v___x_239_ = lean_string_utf8_extract(v_str_235_, v___x_237_, v___x_238_);
    crate::leanh::lean_dec(v___x_238_);
    crate::leanh::lean_dec(v___x_237_);
    return v___x_239_;
}
pub unsafe fn l_String_Slice_Subslice_copy___boxed(
    mut v_s_240_: *mut crate::leanh::LeanObject,
    mut v_sl_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_String_Slice_Subslice_copy(v_s_240_, v_sl_241_);
    crate::leanh::lean_dec_ref(v_sl_241_);
    crate::leanh::lean_dec_ref(v_s_240_);
    return v_res_242_;
}
pub unsafe fn l_String_Slice_Subslice_toString(
    mut v_s_243_: *mut crate::leanh::LeanObject,
    mut v_sl_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_245_ = crate::leanh::lean_ctor_get(v_sl_244_, 0);
    v_endExclusive_246_ = crate::leanh::lean_ctor_get(v_sl_244_, 1);
    v_str_247_ = crate::leanh::lean_ctor_get(v_s_243_, 0);
    v_startInclusive_248_ = crate::leanh::lean_ctor_get(v_s_243_, 1);
    v___x_249_ = lean_nat_add(v_startInclusive_248_, v_startInclusive_245_);
    v___x_250_ = lean_nat_add(v_startInclusive_248_, v_endExclusive_246_);
    v___x_251_ = lean_string_utf8_extract(v_str_247_, v___x_249_, v___x_250_);
    crate::leanh::lean_dec(v___x_250_);
    crate::leanh::lean_dec(v___x_249_);
    return v___x_251_;
}
pub unsafe fn l_String_Slice_Subslice_toString___boxed(
    mut v_s_252_: *mut crate::leanh::LeanObject,
    mut v_sl_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_String_Slice_Subslice_toString(v_s_252_, v_sl_253_);
    crate::leanh::lean_dec_ref(v_sl_253_);
    crate::leanh::lean_dec_ref(v_s_252_);
    return v_res_254_;
}
pub unsafe fn l_String_Slice_Subslice_instToString(
    mut v_s_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_256_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Subslice_toString___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_256_, 0, v_s_255_);
    return v___x_256_;
}
pub unsafe fn l_String_Slice_subslice___redArg(
    mut v_newStart_257_: *mut crate::leanh::LeanObject,
    mut v_newEnd_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_259_, 0, v_newStart_257_);
    crate::leanh::lean_ctor_set(v___x_259_, 1, v_newEnd_258_);
    return v___x_259_;
}
pub unsafe fn l_String_Slice_subslice(
    mut v_s_260_: *mut crate::leanh::LeanObject,
    mut v_newStart_261_: *mut crate::leanh::LeanObject,
    mut v_newEnd_262_: *mut crate::leanh::LeanObject,
    mut v_h_263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_264_, 0, v_newStart_261_);
    crate::leanh::lean_ctor_set(v___x_264_, 1, v_newEnd_262_);
    return v___x_264_;
}
pub unsafe fn l_String_Slice_subslice___boxed(
    mut v_s_265_: *mut crate::leanh::LeanObject,
    mut v_newStart_266_: *mut crate::leanh::LeanObject,
    mut v_newEnd_267_: *mut crate::leanh::LeanObject,
    mut v_h_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_String_Slice_subslice(v_s_265_, v_newStart_266_, v_newEnd_267_, v_h_268_);
    crate::leanh::lean_dec_ref(v_s_265_);
    return v_res_269_;
}
pub unsafe fn l_panic___at___00String_Slice_subslice_x21_spec__0(
    mut v_s_270_: *mut crate::leanh::LeanObject,
    mut v_msg_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = l_String_Slice_instInhabitedSubslice(v_s_270_);
    v___x_273_ = lean_panic_fn_borrowed(v___x_272_, v_msg_271_);
    crate::leanh::lean_dec_ref(v___x_272_);
    return v___x_273_;
}
pub unsafe fn l_panic___at___00String_Slice_subslice_x21_spec__0___boxed(
    mut v_s_274_: *mut crate::leanh::LeanObject,
    mut v_msg_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_panic___at___00String_Slice_subslice_x21_spec__0(v_s_274_, v_msg_275_);
    crate::leanh::lean_dec_ref(v_s_274_);
    return v_res_276_;
}
pub unsafe fn _init_l_String_Slice_subslice_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = l_String_Slice_subslice_x21___closed__2;
    v___x_281_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_282_ = crate::leanh::lean_unsigned_to_nat(128);
    v___x_283_ = l_String_Slice_subslice_x21___closed__1;
    v___x_284_ = l_String_Slice_subslice_x21___closed__0;
    v___x_285_ =
        l_mkPanicMessageWithDecl(v___x_284_, v___x_283_, v___x_282_, v___x_281_, v___x_280_);
    return v___x_285_;
}
pub unsafe fn l_String_Slice_subslice_x21(
    mut v_s_286_: *mut crate::leanh::LeanObject,
    mut v_newStart_287_: *mut crate::leanh::LeanObject,
    mut v_newEnd_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_289_: u8 = 0;
    v___x_289_ = lean_nat_dec_le(v_newStart_287_, v_newEnd_288_);
    if v___x_289_ == 0 {
        let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_newEnd_288_);
        crate::leanh::lean_dec(v_newStart_287_);
        v___x_290_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_subslice_x21___closed__3),
            core::ptr::addr_of_mut!(l_String_Slice_subslice_x21___closed__3_once),
            _init_l_String_Slice_subslice_x21___closed__3,
        );
        v___x_291_ = l_panic___at___00String_Slice_subslice_x21_spec__0(v_s_286_, v___x_290_);
        return v___x_291_;
    } else {
        let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_292_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_292_, 0, v_newStart_287_);
        crate::leanh::lean_ctor_set(v___x_292_, 1, v_newEnd_288_);
        return v___x_292_;
    }
}
pub unsafe fn l_String_Slice_subslice_x21___boxed(
    mut v_s_293_: *mut crate::leanh::LeanObject,
    mut v_newStart_294_: *mut crate::leanh::LeanObject,
    mut v_newEnd_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_String_Slice_subslice_x21(v_s_293_, v_newStart_294_, v_newEnd_295_);
    crate::leanh::lean_dec_ref(v_s_293_);
    return v_res_296_;
}
pub unsafe fn l_String_Slice_subsliceFrom(
    mut v_s_297_: *mut crate::leanh::LeanObject,
    mut v_newStart_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_299_ = crate::leanh::lean_ctor_get(v_s_297_, 1);
    v_endExclusive_300_ = crate::leanh::lean_ctor_get(v_s_297_, 2);
    v___x_301_ = lean_nat_sub(v_endExclusive_300_, v_startInclusive_299_);
    v___x_302_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_302_, 0, v_newStart_298_);
    crate::leanh::lean_ctor_set(v___x_302_, 1, v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_String_Slice_subsliceFrom___boxed(
    mut v_s_303_: *mut crate::leanh::LeanObject,
    mut v_newStart_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ = l_String_Slice_subsliceFrom(v_s_303_, v_newStart_304_);
    crate::leanh::lean_dec_ref(v_s_303_);
    return v_res_305_;
}
pub unsafe fn l_String_Slice_toSubslice(
    mut v_s_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_307_ = crate::leanh::lean_ctor_get(v_s_306_, 1);
    v_endExclusive_308_ = crate::leanh::lean_ctor_get(v_s_306_, 2);
    v___x_309_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_310_ = lean_nat_sub(v_endExclusive_308_, v_startInclusive_307_);
    v___x_311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_311_, 0, v___x_309_);
    crate::leanh::lean_ctor_set(v___x_311_, 1, v___x_310_);
    return v___x_311_;
}
pub unsafe fn l_String_Slice_toSubslice___boxed(
    mut v_s_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_String_Slice_toSubslice(v_s_312_);
    crate::leanh::lean_dec_ref(v_s_312_);
    return v_res_313_;
}
pub unsafe fn l_String_Slice_Subslice_ofSliceFrom___redArg(
    mut v_p_314_: *mut crate::leanh::LeanObject,
    mut v_sl_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_320_: u8 = 0;
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_316_ = crate::leanh::lean_ctor_get(v_sl_315_, 0);
                v_endExclusive_317_ = crate::leanh::lean_ctor_get(v_sl_315_, 1);
                v_isSharedCheck_326_ = (!crate::leanh::lean_is_exclusive(v_sl_315_)) as u8;
                if v_isSharedCheck_326_ == 0 {
                    v___x_319_ = v_sl_315_;
                    v_isShared_320_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_317_);
                    crate::leanh::lean_inc(v_startInclusive_316_);
                    crate::leanh::lean_dec(v_sl_315_);
                    v___x_319_ = crate::leanh::lean_box(0);
                    v_isShared_320_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_321_ = lean_nat_add(v_p_314_, v_startInclusive_316_);
                crate::leanh::lean_dec(v_startInclusive_316_);
                v___x_322_ = lean_nat_add(v_p_314_, v_endExclusive_317_);
                crate::leanh::lean_dec(v_endExclusive_317_);
                if v_isShared_320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_319_, 1, v___x_322_);
                    crate::leanh::lean_ctor_set(v___x_319_, 0, v___x_321_);
                    v___x_324_ = v___x_319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_325_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
                    v___x_324_ = v_reuseFailAlloc_325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_ofSliceFrom___redArg___boxed(
    mut v_p_327_: *mut crate::leanh::LeanObject,
    mut v_sl_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_329_ = l_String_Slice_Subslice_ofSliceFrom___redArg(v_p_327_, v_sl_328_);
    crate::leanh::lean_dec(v_p_327_);
    return v_res_329_;
}
pub unsafe fn l_String_Slice_Subslice_ofSliceFrom(
    mut v_s_330_: *mut crate::leanh::LeanObject,
    mut v_p_331_: *mut crate::leanh::LeanObject,
    mut v_sl_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_337_: u8 = 0;
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_333_ = crate::leanh::lean_ctor_get(v_sl_332_, 0);
                v_endExclusive_334_ = crate::leanh::lean_ctor_get(v_sl_332_, 1);
                v_isSharedCheck_343_ = (!crate::leanh::lean_is_exclusive(v_sl_332_)) as u8;
                if v_isSharedCheck_343_ == 0 {
                    v___x_336_ = v_sl_332_;
                    v_isShared_337_ = v_isSharedCheck_343_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_334_);
                    crate::leanh::lean_inc(v_startInclusive_333_);
                    crate::leanh::lean_dec(v_sl_332_);
                    v___x_336_ = crate::leanh::lean_box(0);
                    v_isShared_337_ = v_isSharedCheck_343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_338_ = lean_nat_add(v_p_331_, v_startInclusive_333_);
                crate::leanh::lean_dec(v_startInclusive_333_);
                v___x_339_ = lean_nat_add(v_p_331_, v_endExclusive_334_);
                crate::leanh::lean_dec(v_endExclusive_334_);
                if v_isShared_337_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_336_, 1, v___x_339_);
                    crate::leanh::lean_ctor_set(v___x_336_, 0, v___x_338_);
                    v___x_341_ = v___x_336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_339_);
                    v___x_341_ = v_reuseFailAlloc_342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_ofSliceFrom___boxed(
    mut v_s_344_: *mut crate::leanh::LeanObject,
    mut v_p_345_: *mut crate::leanh::LeanObject,
    mut v_sl_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_String_Slice_Subslice_ofSliceFrom(v_s_344_, v_p_345_, v_sl_346_);
    crate::leanh::lean_dec(v_p_345_);
    crate::leanh::lean_dec_ref(v_s_344_);
    return v_res_347_;
}
pub unsafe fn l_String_Slice_Subslice_extendLeft___redArg(
    mut v_sl_348_: *mut crate::leanh::LeanObject,
    mut v_newStart_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_endExclusive_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_357_: u8 = 0;
    let mut v_unused_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_endExclusive_350_ = crate::leanh::lean_ctor_get(v_sl_348_, 1);
                v_isSharedCheck_357_ = (!crate::leanh::lean_is_exclusive(v_sl_348_)) as u8;
                if v_isSharedCheck_357_ == 0 {
                    v_unused_358_ = crate::leanh::lean_ctor_get(v_sl_348_, 0);
                    crate::leanh::lean_dec(v_unused_358_);
                    v___x_352_ = v_sl_348_;
                    v_isShared_353_ = v_isSharedCheck_357_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_350_);
                    crate::leanh::lean_dec(v_sl_348_);
                    v___x_352_ = crate::leanh::lean_box(0);
                    v_isShared_353_ = v_isSharedCheck_357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_352_, 0, v_newStart_349_);
                    v___x_355_ = v___x_352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_356_, 0, v_newStart_349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_356_, 1, v_endExclusive_350_);
                    v___x_355_ = v_reuseFailAlloc_356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_extendLeft(
    mut v_s_359_: *mut crate::leanh::LeanObject,
    mut v_sl_360_: *mut crate::leanh::LeanObject,
    mut v_newStart_361_: *mut crate::leanh::LeanObject,
    mut v_h_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_endExclusive_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_370_: u8 = 0;
    let mut v_unused_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_endExclusive_363_ = crate::leanh::lean_ctor_get(v_sl_360_, 1);
                v_isSharedCheck_370_ = (!crate::leanh::lean_is_exclusive(v_sl_360_)) as u8;
                if v_isSharedCheck_370_ == 0 {
                    v_unused_371_ = crate::leanh::lean_ctor_get(v_sl_360_, 0);
                    crate::leanh::lean_dec(v_unused_371_);
                    v___x_365_ = v_sl_360_;
                    v_isShared_366_ = v_isSharedCheck_370_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_363_);
                    crate::leanh::lean_dec(v_sl_360_);
                    v___x_365_ = crate::leanh::lean_box(0);
                    v_isShared_366_ = v_isSharedCheck_370_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_365_, 0, v_newStart_361_);
                    v___x_368_ = v___x_365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_369_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_369_, 0, v_newStart_361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_369_, 1, v_endExclusive_363_);
                    v___x_368_ = v_reuseFailAlloc_369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_extendLeft___boxed(
    mut v_s_372_: *mut crate::leanh::LeanObject,
    mut v_sl_373_: *mut crate::leanh::LeanObject,
    mut v_newStart_374_: *mut crate::leanh::LeanObject,
    mut v_h_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l_String_Slice_Subslice_extendLeft(v_s_372_, v_sl_373_, v_newStart_374_, v_h_375_);
    crate::leanh::lean_dec_ref(v_s_372_);
    return v_res_376_;
}
pub unsafe fn l_String_Slice_Subslice_cast___redArg(
    mut v_sl_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_382_: u8 = 0;
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_378_ = crate::leanh::lean_ctor_get(v_sl_377_, 0);
                v_endExclusive_379_ = crate::leanh::lean_ctor_get(v_sl_377_, 1);
                v_isSharedCheck_386_ = (!crate::leanh::lean_is_exclusive(v_sl_377_)) as u8;
                if v_isSharedCheck_386_ == 0 {
                    v___x_381_ = v_sl_377_;
                    v_isShared_382_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_379_);
                    crate::leanh::lean_inc(v_startInclusive_378_);
                    crate::leanh::lean_dec(v_sl_377_);
                    v___x_381_ = crate::leanh::lean_box(0);
                    v_isShared_382_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_382_ == 0 {
                    v___x_384_ = v___x_381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 0, v_startInclusive_378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_385_, 1, v_endExclusive_379_);
                    v___x_384_ = v_reuseFailAlloc_385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_cast(
    mut v_s_387_: *mut crate::leanh::LeanObject,
    mut v_t_388_: *mut crate::leanh::LeanObject,
    mut v_h_389_: *mut crate::leanh::LeanObject,
    mut v_sl_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_391_ = crate::leanh::lean_ctor_get(v_sl_390_, 0);
                v_endExclusive_392_ = crate::leanh::lean_ctor_get(v_sl_390_, 1);
                v_isSharedCheck_399_ = (!crate::leanh::lean_is_exclusive(v_sl_390_)) as u8;
                if v_isSharedCheck_399_ == 0 {
                    v___x_394_ = v_sl_390_;
                    v_isShared_395_ = v_isSharedCheck_399_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_392_);
                    crate::leanh::lean_inc(v_startInclusive_391_);
                    crate::leanh::lean_dec(v_sl_390_);
                    v___x_394_ = crate::leanh::lean_box(0);
                    v_isShared_395_ = v_isSharedCheck_399_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_395_ == 0 {
                    v___x_397_ = v___x_394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_398_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 0, v_startInclusive_391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 1, v_endExclusive_392_);
                    v___x_397_ = v_reuseFailAlloc_398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Subslice_cast___boxed(
    mut v_s_400_: *mut crate::leanh::LeanObject,
    mut v_t_401_: *mut crate::leanh::LeanObject,
    mut v_h_402_: *mut crate::leanh::LeanObject,
    mut v_sl_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l_String_Slice_Subslice_cast(v_s_400_, v_t_401_, v_h_402_, v_sl_403_);
    crate::leanh::lean_dec_ref(v_t_401_);
    crate::leanh::lean_dec_ref(v_s_400_);
    return v_res_404_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Subslice(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Subslice(
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
pub unsafe fn initialize_Init_Data_String_Subslice(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Subslice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Subslice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Subslice(builtin);
}
