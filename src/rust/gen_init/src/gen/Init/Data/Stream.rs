// Lean compiler output
// Module: Init.Data.Stream
// Imports: Init.Data.Range Init.Data.Array.Subarray Init.Data.Slice.Array.Basic
use crate::r#gen::Init::Data::Array::Subarray::{
    initialize_Init_Data_Array_Subarray, l_Array_toSubarray___redArg,
    runtime_initialize_Init_Data_Array_Subarray,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::Slice::Array::Basic::{
    initialize_Init_Data_Slice_Array_Basic, runtime_initialize_Init_Data_Slice_Array_Basic,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_lt, lean_string_utf8_byte_size,
};
pub static l_Std_instToStreamList___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instToStreamList___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToStreamList___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamList___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_instToStreamArraySubarray___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instToStreamArraySubarray___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToStreamArraySubarray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamArraySubarray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_instToStreamSubarray___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instToStreamSubarray___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToStreamSubarray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamSubarray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_instToStreamStringRaw___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instToStreamStringRaw___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToStreamStringRaw___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamStringRaw___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_instToStreamStringRaw: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamStringRaw___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_instToStreamRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instToStreamRange___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToStreamRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamRange___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Std_instToStreamRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStreamRange___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_instStreamList___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instStreamList___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instStreamList___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instStreamList___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_instStreamSubarray___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instStreamSubarray___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instStreamSubarray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instStreamSubarray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_instStreamRangeNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_instStreamRangeNat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instStreamRangeNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instStreamRangeNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_instStreamRangeNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instStreamRangeNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(
    mut v_inst_222_: *mut crate::leanh::LeanObject,
    mut v_inst_223_: *mut crate::leanh::LeanObject,
    mut v_f_224_: *mut crate::leanh::LeanObject,
    mut v_s_225_: *mut crate::leanh::LeanObject,
    mut v_b_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_227_ = crate::leanh::lean_ctor_get(v_inst_223_, 0);
    v_toBind_228_ = crate::leanh::lean_ctor_get(v_inst_223_, 1);
    crate::leanh::lean_inc(v_toBind_228_);
    v_toPure_229_ = crate::leanh::lean_ctor_get(v_toApplicative_227_, 1);
    crate::leanh::lean_inc(v_toPure_229_);
    crate::leanh::lean_inc_ref(v_inst_222_);
    v___x_230_ = crate::leanh::lean_apply_1(v_inst_222_, v_s_225_);
    if crate::leanh::lean_obj_tag(v___x_230_) == 0 {
        let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_228_);
        crate::leanh::lean_dec(v_f_224_);
        crate::leanh::lean_dec_ref(v_inst_223_);
        crate::leanh::lean_dec_ref(v_inst_222_);
        v___x_231_ = crate::leanh::lean_apply_2(v_toPure_229_, crate::leanh::lean_box(0), v_b_226_);
        return v___x_231_;
    } else {
        let mut v_val_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_232_ = crate::leanh::lean_ctor_get(v___x_230_, 0);
        crate::leanh::lean_inc(v_val_232_);
        crate::leanh::lean_dec_ref_known(v___x_230_, 1);
        v_fst_233_ = crate::leanh::lean_ctor_get(v_val_232_, 0);
        crate::leanh::lean_inc(v_fst_233_);
        v_snd_234_ = crate::leanh::lean_ctor_get(v_val_232_, 1);
        crate::leanh::lean_inc(v_snd_234_);
        crate::leanh::lean_dec(v_val_232_);
        crate::leanh::lean_inc(v_f_224_);
        v___f_235_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_235_, 0, v_toPure_229_);
        crate::leanh::lean_closure_set(v___f_235_, 1, v_inst_222_);
        crate::leanh::lean_closure_set(v___f_235_, 2, v_inst_223_);
        crate::leanh::lean_closure_set(v___f_235_, 3, v_f_224_);
        crate::leanh::lean_closure_set(v___f_235_, 4, v_snd_234_);
        v___x_236_ = crate::leanh::lean_apply_2(v_f_224_, v_fst_233_, v_b_226_);
        v___x_237_ = crate::leanh::lean_apply_4(
            v_toBind_228_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_236_,
            v___f_235_,
        );
        return v___x_237_;
    }
}
pub unsafe fn l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg___lam__0(
    mut v_toPure_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_inst_240_: *mut crate::leanh::LeanObject,
    mut v_f_241_: *mut crate::leanh::LeanObject,
    mut v_snd_242_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_243_) == 0 {
        let mut v_a_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_snd_242_);
        crate::leanh::lean_dec(v_f_241_);
        crate::leanh::lean_dec_ref(v_inst_240_);
        crate::leanh::lean_dec_ref(v_inst_239_);
        v_a_244_ = crate::leanh::lean_ctor_get(v_____do__lift_243_, 0);
        crate::leanh::lean_inc(v_a_244_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_243_, 1);
        v___x_245_ = crate::leanh::lean_apply_2(v_toPure_238_, crate::leanh::lean_box(0), v_a_244_);
        return v___x_245_;
    } else {
        let mut v_a_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_238_);
        v_a_246_ = crate::leanh::lean_ctor_get(v_____do__lift_243_, 0);
        crate::leanh::lean_inc(v_a_246_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_243_, 1);
        v___x_247_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(
            v_inst_239_,
            v_inst_240_,
            v_f_241_,
            v_snd_242_,
            v_a_246_,
        );
        return v___x_247_;
    }
}
pub unsafe fn l___private_Init_Data_Stream_0__Std_Stream_forIn_visit(
    mut v_00_u03c1_248_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_249_: *mut crate::leanh::LeanObject,
    mut v_m_250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
    mut v_inst_253_: *mut crate::leanh::LeanObject,
    mut v_f_254_: *mut crate::leanh::LeanObject,
    mut v_s_255_: *mut crate::leanh::LeanObject,
    mut v_b_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(
        v_inst_252_,
        v_inst_253_,
        v_f_254_,
        v_s_255_,
        v_b_256_,
    );
    return v___x_257_;
}
pub unsafe fn l_Std_Stream_forIn___redArg(
    mut v_inst_258_: *mut crate::leanh::LeanObject,
    mut v_inst_259_: *mut crate::leanh::LeanObject,
    mut v_s_260_: *mut crate::leanh::LeanObject,
    mut v_b_261_: *mut crate::leanh::LeanObject,
    mut v_f_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(
        v_inst_258_,
        v_inst_259_,
        v_f_262_,
        v_s_260_,
        v_b_261_,
    );
    return v___x_263_;
}
pub unsafe fn l_Std_Stream_forIn(
    mut v_00_u03c1_264_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_265_: *mut crate::leanh::LeanObject,
    mut v_m_266_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_267_: *mut crate::leanh::LeanObject,
    mut v_inst_268_: *mut crate::leanh::LeanObject,
    mut v_inst_269_: *mut crate::leanh::LeanObject,
    mut v_s_270_: *mut crate::leanh::LeanObject,
    mut v_b_271_: *mut crate::leanh::LeanObject,
    mut v_f_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_273_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(
        v_inst_268_,
        v_inst_269_,
        v_f_272_,
        v_s_270_,
        v_b_271_,
    );
    return v___x_273_;
}
pub unsafe fn l_Std_instForInOfMonadOfStream___redArg___lam__0(
    mut v_inst_274_: *mut crate::leanh::LeanObject,
    mut v_inst_275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_276_: *mut crate::leanh::LeanObject,
    mut v___y_277_: *mut crate::leanh::LeanObject,
    mut v___y_278_: *mut crate::leanh::LeanObject,
    mut v___y_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___redArg(
        v_inst_274_,
        v_inst_275_,
        v___y_279_,
        v___y_277_,
        v___y_278_,
    );
    return v___x_280_;
}
pub unsafe fn l_Std_instForInOfMonadOfStream___redArg(
    mut v_inst_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_283_ = crate::leanh::lean_alloc_closure(
        l_Std_instForInOfMonadOfStream___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_283_, 0, v_inst_282_);
    crate::leanh::lean_closure_set(v___f_283_, 1, v_inst_281_);
    return v___f_283_;
}
pub unsafe fn l_Std_instForInOfMonadOfStream(
    mut v_m_284_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_inst_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_289_ = crate::leanh::lean_alloc_closure(
        l_Std_instForInOfMonadOfStream___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_289_, 0, v_inst_288_);
    crate::leanh::lean_closure_set(v___f_289_, 1, v_inst_287_);
    return v___f_289_;
}
pub unsafe fn l_Std_instToStreamList___lam__0(
    mut v_c_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_c_290_);
    return v_c_290_;
}
pub unsafe fn l_Std_instToStreamList___lam__0___boxed(
    mut v_c_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_292_ = l_Std_instToStreamList___lam__0(v_c_291_);
    crate::leanh::lean_dec(v_c_291_);
    return v_res_292_;
}
pub unsafe fn l_Std_instToStreamList(
    mut v_00_u03b1_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_295_ = l_Std_instToStreamList___closed__0;
    return v___f_295_;
}
pub unsafe fn l_Std_instToStreamArraySubarray___lam__0(
    mut v_a_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_298_ = lean_array_get_size(v_a_296_);
    v___x_299_ = l_Array_toSubarray___redArg(v_a_296_, v___x_297_, v___x_298_);
    return v___x_299_;
}
pub unsafe fn l_Std_instToStreamArraySubarray(
    mut v_00_u03b1_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_302_ = l_Std_instToStreamArraySubarray___closed__0;
    return v___f_302_;
}
pub unsafe fn l_Std_instToStreamSubarray___lam__0(
    mut v_a_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_a_303_);
    return v_a_303_;
}
pub unsafe fn l_Std_instToStreamSubarray___lam__0___boxed(
    mut v_a_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ = l_Std_instToStreamSubarray___lam__0(v_a_304_);
    crate::leanh::lean_dec_ref(v_a_304_);
    return v_res_305_;
}
pub unsafe fn l_Std_instToStreamSubarray(
    mut v_00_u03b1_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_308_ = l_Std_instToStreamSubarray___closed__0;
    return v___f_308_;
}
pub unsafe fn l_Std_instToStreamStringRaw___lam__0(
    mut v_s_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_311_ = lean_string_utf8_byte_size(v_s_309_);
    v___x_312_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_312_, 0, v_s_309_);
    crate::leanh::lean_ctor_set(v___x_312_, 1, v___x_310_);
    crate::leanh::lean_ctor_set(v___x_312_, 2, v___x_311_);
    return v___x_312_;
}
pub unsafe fn l_Std_instToStreamRange___lam__0(
    mut v_r_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_r_315_);
    return v_r_315_;
}
pub unsafe fn l_Std_instToStreamRange___lam__0___boxed(
    mut v_r_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_instToStreamRange___lam__0(v_r_316_);
    crate::leanh::lean_dec_ref(v_r_316_);
    return v_res_317_;
}
pub unsafe fn l_Std_instStreamProd___redArg___lam__0(
    mut v_inst_320_: *mut crate::leanh::LeanObject,
    mut v_inst_321_: *mut crate::leanh::LeanObject,
    mut v_x_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_327_: u8 = 0;
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_335_: u8 = 0;
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_341_: u8 = 0;
    let mut v_fst_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_359_: u8 = 0;
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut v_isSharedCheck_361_: u8 = 0;
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_323_ = crate::leanh::lean_ctor_get(v_x_322_, 0);
                v_snd_324_ = crate::leanh::lean_ctor_get(v_x_322_, 1);
                v_isSharedCheck_362_ = (!crate::leanh::lean_is_exclusive(v_x_322_)) as u8;
                if v_isSharedCheck_362_ == 0 {
                    v___x_326_ = v_x_322_;
                    v_isShared_327_ = v_isSharedCheck_362_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_324_);
                    crate::leanh::lean_inc(v_fst_323_);
                    crate::leanh::lean_dec(v_x_322_);
                    v___x_326_ = crate::leanh::lean_box(0);
                    v_isShared_327_ = v_isSharedCheck_362_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_328_ = crate::leanh::lean_apply_1(v_inst_320_, v_fst_323_);
                if crate::leanh::lean_obj_tag(v___x_328_) == 0 {
                    crate::leanh::lean_del_object(v___x_326_);
                    crate::leanh::lean_dec(v_snd_324_);
                    crate::leanh::lean_dec_ref(v_inst_321_);
                    v___x_329_ = crate::leanh::lean_box(0);
                    return v___x_329_;
                } else {
                    v_val_330_ = crate::leanh::lean_ctor_get(v___x_328_, 0);
                    crate::leanh::lean_inc(v_val_330_);
                    crate::leanh::lean_dec_ref_known(v___x_328_, 1);
                    v_fst_331_ = crate::leanh::lean_ctor_get(v_val_330_, 0);
                    v_snd_332_ = crate::leanh::lean_ctor_get(v_val_330_, 1);
                    v_isSharedCheck_361_ = (!crate::leanh::lean_is_exclusive(v_val_330_)) as u8;
                    if v_isSharedCheck_361_ == 0 {
                        v___x_334_ = v_val_330_;
                        v_isShared_335_ = v_isSharedCheck_361_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_332_);
                        crate::leanh::lean_inc(v_fst_331_);
                        crate::leanh::lean_dec(v_val_330_);
                        v___x_334_ = crate::leanh::lean_box(0);
                        v_isShared_335_ = v_isSharedCheck_361_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_336_ = crate::leanh::lean_apply_1(v_inst_321_, v_snd_324_);
                if crate::leanh::lean_obj_tag(v___x_336_) == 0 {
                    crate::leanh::lean_del_object(v___x_334_);
                    crate::leanh::lean_dec(v_snd_332_);
                    crate::leanh::lean_dec(v_fst_331_);
                    crate::leanh::lean_del_object(v___x_326_);
                    v___x_337_ = crate::leanh::lean_box(0);
                    return v___x_337_;
                } else {
                    v_val_338_ = crate::leanh::lean_ctor_get(v___x_336_, 0);
                    v_isSharedCheck_360_ = (!crate::leanh::lean_is_exclusive(v___x_336_)) as u8;
                    if v_isSharedCheck_360_ == 0 {
                        v___x_340_ = v___x_336_;
                        v_isShared_341_ = v_isSharedCheck_360_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_338_);
                        crate::leanh::lean_dec(v___x_336_);
                        v___x_340_ = crate::leanh::lean_box(0);
                        v_isShared_341_ = v_isSharedCheck_360_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_342_ = crate::leanh::lean_ctor_get(v_val_338_, 0);
                v_snd_343_ = crate::leanh::lean_ctor_get(v_val_338_, 1);
                v_isSharedCheck_359_ = (!crate::leanh::lean_is_exclusive(v_val_338_)) as u8;
                if v_isSharedCheck_359_ == 0 {
                    v___x_345_ = v_val_338_;
                    v_isShared_346_ = v_isSharedCheck_359_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_343_);
                    crate::leanh::lean_inc(v_fst_342_);
                    crate::leanh::lean_dec(v_val_338_);
                    v___x_345_ = crate::leanh::lean_box(0);
                    v_isShared_346_ = v_isSharedCheck_359_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_345_, 1, v_fst_342_);
                    crate::leanh::lean_ctor_set(v___x_345_, 0, v_fst_331_);
                    v___x_348_ = v___x_345_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_358_, 0, v_fst_331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_358_, 1, v_fst_342_);
                    v___x_348_ = v_reuseFailAlloc_358_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_334_, 1, v_snd_343_);
                    crate::leanh::lean_ctor_set(v___x_334_, 0, v_snd_332_);
                    v___x_350_ = v___x_334_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_357_, 0, v_snd_332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_357_, 1, v_snd_343_);
                    v___x_350_ = v_reuseFailAlloc_357_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_326_, 1, v___x_350_);
                    crate::leanh::lean_ctor_set(v___x_326_, 0, v___x_348_);
                    v___x_352_ = v___x_326_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_350_);
                    v___x_352_ = v_reuseFailAlloc_356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_352_);
                    v___x_354_ = v___x_340_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
                    v___x_354_ = v_reuseFailAlloc_355_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instStreamProd___redArg(
    mut v_inst_363_: *mut crate::leanh::LeanObject,
    mut v_inst_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_365_ = crate::leanh::lean_alloc_closure(
        l_Std_instStreamProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_365_, 0, v_inst_363_);
    crate::leanh::lean_closure_set(v___f_365_, 1, v_inst_364_);
    return v___f_365_;
}
pub unsafe fn l_Std_instStreamProd(
    mut v_00_u03c1_366_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_368_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_369_: *mut crate::leanh::LeanObject,
    mut v_inst_370_: *mut crate::leanh::LeanObject,
    mut v_inst_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_372_ = crate::leanh::lean_alloc_closure(
        l_Std_instStreamProd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_372_, 0, v_inst_370_);
    crate::leanh::lean_closure_set(v___f_372_, 1, v_inst_371_);
    return v___f_372_;
}
pub unsafe fn l_Std_instStreamList___lam__0(
    mut v_x_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_379_: u8 = 0;
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_373_) == 0 {
                    v___x_374_ = crate::leanh::lean_box(0);
                    return v___x_374_;
                } else {
                    v_head_375_ = crate::leanh::lean_ctor_get(v_x_373_, 0);
                    v_tail_376_ = crate::leanh::lean_ctor_get(v_x_373_, 1);
                    v_isSharedCheck_384_ = (!crate::leanh::lean_is_exclusive(v_x_373_)) as u8;
                    if v_isSharedCheck_384_ == 0 {
                        v___x_378_ = v_x_373_;
                        v_isShared_379_ = v_isSharedCheck_384_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_376_);
                        crate::leanh::lean_inc(v_head_375_);
                        crate::leanh::lean_dec(v_x_373_);
                        v___x_378_ = crate::leanh::lean_box(0);
                        v_isShared_379_ = v_isSharedCheck_384_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_379_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_378_, 0);
                    v___x_381_ = v___x_378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_383_, 0, v_head_375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_383_, 1, v_tail_376_);
                    v___x_381_ = v_reuseFailAlloc_383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_382_, 0, v___x_381_);
                return v___x_382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instStreamList(
    mut v_00_u03b1_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_387_ = l_Std_instStreamList___closed__0;
    return v___f_387_;
}
pub unsafe fn l_Std_instStreamSubarray___lam__0(
    mut v_s_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_394_: u8 = 0;
    let mut v___x_395_: u8 = 0;
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_389_ = crate::leanh::lean_ctor_get(v_s_388_, 0);
                v_start_390_ = crate::leanh::lean_ctor_get(v_s_388_, 1);
                v_stop_391_ = crate::leanh::lean_ctor_get(v_s_388_, 2);
                v_isSharedCheck_405_ = (!crate::leanh::lean_is_exclusive(v_s_388_)) as u8;
                if v_isSharedCheck_405_ == 0 {
                    v___x_393_ = v_s_388_;
                    v_isShared_394_ = v_isSharedCheck_405_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_391_);
                    crate::leanh::lean_inc(v_start_390_);
                    crate::leanh::lean_inc(v_array_389_);
                    crate::leanh::lean_dec(v_s_388_);
                    v___x_393_ = crate::leanh::lean_box(0);
                    v_isShared_394_ = v_isSharedCheck_405_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_395_ = lean_nat_dec_lt(v_start_390_, v_stop_391_);
                if v___x_395_ == 0 {
                    crate::leanh::lean_del_object(v___x_393_);
                    crate::leanh::lean_dec(v_stop_391_);
                    crate::leanh::lean_dec(v_start_390_);
                    crate::leanh::lean_dec_ref(v_array_389_);
                    v___x_396_ = crate::leanh::lean_box(0);
                    return v___x_396_;
                } else {
                    v___x_397_ = lean_array_fget(v_array_389_, v_start_390_);
                    v___x_398_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_399_ = lean_nat_add(v_start_390_, v___x_398_);
                    crate::leanh::lean_dec(v_start_390_);
                    if v_isShared_394_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_393_, 1, v___x_399_);
                        v___x_401_ = v___x_393_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_404_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v_array_389_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_399_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_404_, 2, v_stop_391_);
                        v___x_401_ = v_reuseFailAlloc_404_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_402_, 0, v___x_397_);
                crate::leanh::lean_ctor_set(v___x_402_, 1, v___x_401_);
                v___x_403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_403_, 0, v___x_402_);
                return v___x_403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instStreamSubarray(
    mut v_00_u03b1_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_408_ = l_Std_instStreamSubarray___closed__0;
    return v___f_408_;
}
pub unsafe fn l_Std_instStreamRangeNat___lam__0(
    mut v_r_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_416_: u8 = 0;
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_410_ = crate::leanh::lean_ctor_get(v_r_409_, 0);
                v_stop_411_ = crate::leanh::lean_ctor_get(v_r_409_, 1);
                v_step_412_ = crate::leanh::lean_ctor_get(v_r_409_, 2);
                v_isSharedCheck_424_ = (!crate::leanh::lean_is_exclusive(v_r_409_)) as u8;
                if v_isSharedCheck_424_ == 0 {
                    v___x_414_ = v_r_409_;
                    v_isShared_415_ = v_isSharedCheck_424_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_step_412_);
                    crate::leanh::lean_inc(v_stop_411_);
                    crate::leanh::lean_inc(v_start_410_);
                    crate::leanh::lean_dec(v_r_409_);
                    v___x_414_ = crate::leanh::lean_box(0);
                    v_isShared_415_ = v_isSharedCheck_424_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_416_ = lean_nat_dec_lt(v_start_410_, v_stop_411_);
                if v___x_416_ == 0 {
                    crate::leanh::lean_del_object(v___x_414_);
                    crate::leanh::lean_dec(v_step_412_);
                    crate::leanh::lean_dec(v_stop_411_);
                    crate::leanh::lean_dec(v_start_410_);
                    v___x_417_ = crate::leanh::lean_box(0);
                    return v___x_417_;
                } else {
                    v___x_418_ = lean_nat_add(v_start_410_, v_step_412_);
                    if v_isShared_415_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_414_, 0, v___x_418_);
                        v___x_420_ = v___x_414_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_423_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_418_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_423_, 1, v_stop_411_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_423_, 2, v_step_412_);
                        v___x_420_ = v_reuseFailAlloc_423_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_421_, 0, v_start_410_);
                crate::leanh::lean_ctor_set(v___x_421_, 1, v___x_420_);
                v___x_422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
                return v___x_422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Stream_next_x3f___redArg(
    mut v_self_427_: *mut crate::leanh::LeanObject,
    mut v_a_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = crate::leanh::lean_apply_1(v_self_427_, v_a_428_);
    return v___x_429_;
}
pub unsafe fn l_Stream_next_x3f(
    mut v_stream_430_: *mut crate::leanh::LeanObject,
    mut v_value_431_: *mut crate::leanh::LeanObject,
    mut v_self_432_: *mut crate::leanh::LeanObject,
    mut v_a_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_434_ = crate::leanh::lean_apply_1(v_self_432_, v_a_433_);
    return v___x_434_;
}
pub unsafe fn l_ToStream_toStream___redArg(
    mut v_self_435_: *mut crate::leanh::LeanObject,
    mut v_a_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ = crate::leanh::lean_apply_1(v_self_435_, v_a_436_);
    return v___x_437_;
}
pub unsafe fn l_ToStream_toStream(
    mut v_collection_438_: *mut crate::leanh::LeanObject,
    mut v_stream_439_: *mut crate::leanh::LeanObject,
    mut v_self_440_: *mut crate::leanh::LeanObject,
    mut v_a_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = crate::leanh::lean_apply_1(v_self_440_, v_a_441_);
    return v___x_442_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Stream(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Stream(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Stream(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Stream(builtin);
}
