// Lean compiler output
// Module: Lean.Data.RArray
// Imports: Lean.Meta.DecLevel Init.Data.RArray Init.Omega
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Lean::Expr::{l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkRawNatLit};
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, l_Lean_Meta_getDecLevel, runtime_initialize_Lean_Meta_DecLevel,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq,
};
pub static l_Lean_RArray_toExpr___redArg___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_RArray_toExpr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RArray_toExpr___redArg___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [82, 65, 114, 114, 97, 121, 0],
    };
static mut l_Lean_RArray_toExpr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RArray_toExpr___redArg___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [108, 101, 97, 102, 0],
    };
static mut l_Lean_RArray_toExpr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_RArray_toExpr___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_RArray_toExpr___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6242463428107210078 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_RArray_toExpr___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            803888951960056121 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_RArray_toExpr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_RArray_toExpr___redArg___closed__4_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [98, 114, 97, 110, 99, 104, 0],
    };
static mut l_Lean_RArray_toExpr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_RArray_toExpr___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_RArray_toExpr___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6242463428107210078 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_RArray_toExpr___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            5673740600655488943 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_RArray_toExpr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
    mut v_f_214_: *mut crate::leanh::LeanObject,
    mut v_lb_215_: *mut crate::leanh::LeanObject,
    mut v_ub_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u8 = 0;
    v___x_217_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_218_ = lean_nat_add(v_lb_215_, v___x_217_);
    v___x_219_ = lean_nat_dec_eq(v___x_218_, v_ub_216_);
    crate::leanh::lean_dec(v___x_218_);
    if v___x_219_ == 0 {
        let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_mid_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_220_ = lean_nat_add(v_lb_215_, v_ub_216_);
        v_mid_221_ = lean_nat_shiftr(v___x_220_, v___x_217_);
        crate::leanh::lean_dec(v___x_220_);
        crate::leanh::lean_inc(v_f_214_);
        v___x_222_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
            v_f_214_, v_lb_215_, v_mid_221_,
        );
        crate::leanh::lean_inc(v_mid_221_);
        v___x_223_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
            v_f_214_, v_mid_221_, v_ub_216_,
        );
        v___x_224_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_224_, 0, v_mid_221_);
        crate::leanh::lean_ctor_set(v___x_224_, 1, v___x_222_);
        crate::leanh::lean_ctor_set(v___x_224_, 2, v___x_223_);
        return v___x_224_;
    } else {
        let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_225_ = crate::leanh::lean_apply_1(v_f_214_, v_lb_215_);
        v___x_226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_226_, 0, v___x_225_);
        return v___x_226_;
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg___boxed(
    mut v_f_227_: *mut crate::leanh::LeanObject,
    mut v_lb_228_: *mut crate::leanh::LeanObject,
    mut v_ub_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_230_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
        v_f_227_, v_lb_228_, v_ub_229_,
    );
    crate::leanh::lean_dec(v_ub_229_);
    return v_res_230_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(
    mut v_00_u03b1_231_: *mut crate::leanh::LeanObject,
    mut v_n_232_: *mut crate::leanh::LeanObject,
    mut v_f_233_: *mut crate::leanh::LeanObject,
    mut v_lb_234_: *mut crate::leanh::LeanObject,
    mut v_ub_235_: *mut crate::leanh::LeanObject,
    mut v_h1_236_: *mut crate::leanh::LeanObject,
    mut v_h2_237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
        v_f_233_, v_lb_234_, v_ub_235_,
    );
    return v___x_238_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___boxed(
    mut v_00_u03b1_239_: *mut crate::leanh::LeanObject,
    mut v_n_240_: *mut crate::leanh::LeanObject,
    mut v_f_241_: *mut crate::leanh::LeanObject,
    mut v_lb_242_: *mut crate::leanh::LeanObject,
    mut v_ub_243_: *mut crate::leanh::LeanObject,
    mut v_h1_244_: *mut crate::leanh::LeanObject,
    mut v_h2_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(
        v_00_u03b1_239_,
        v_n_240_,
        v_f_241_,
        v_lb_242_,
        v_ub_243_,
        v_h1_244_,
        v_h2_245_,
    );
    crate::leanh::lean_dec(v_ub_243_);
    crate::leanh::lean_dec(v_n_240_);
    return v_res_246_;
}
pub unsafe fn l_Lean_RArray_ofFn___redArg(
    mut v_n_247_: *mut crate::leanh::LeanObject,
    mut v_f_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_249_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_250_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
        v_f_248_, v___x_249_, v_n_247_,
    );
    return v___x_250_;
}
pub unsafe fn l_Lean_RArray_ofFn___redArg___boxed(
    mut v_n_251_: *mut crate::leanh::LeanObject,
    mut v_f_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_253_ = l_Lean_RArray_ofFn___redArg(v_n_251_, v_f_252_);
    crate::leanh::lean_dec(v_n_251_);
    return v_res_253_;
}
pub unsafe fn l_Lean_RArray_ofFn(
    mut v_00_u03b1_254_: *mut crate::leanh::LeanObject,
    mut v_n_255_: *mut crate::leanh::LeanObject,
    mut v_f_256_: *mut crate::leanh::LeanObject,
    mut v_h_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = l_Lean_RArray_ofFn___redArg(v_n_255_, v_f_256_);
    return v___x_258_;
}
pub unsafe fn l_Lean_RArray_ofFn___boxed(
    mut v_00_u03b1_259_: *mut crate::leanh::LeanObject,
    mut v_n_260_: *mut crate::leanh::LeanObject,
    mut v_f_261_: *mut crate::leanh::LeanObject,
    mut v_h_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_263_ = l_Lean_RArray_ofFn(v_00_u03b1_259_, v_n_260_, v_f_261_, v_h_262_);
    crate::leanh::lean_dec(v_n_260_);
    return v_res_263_;
}
pub unsafe fn l_Lean_RArray_ofArray___redArg___lam__0(
    mut v_xs_264_: *mut crate::leanh::LeanObject,
    mut v_x_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = lean_array_fget_borrowed(v_xs_264_, v_x_265_);
    crate::leanh::lean_inc(v___x_266_);
    return v___x_266_;
}
pub unsafe fn l_Lean_RArray_ofArray___redArg___lam__0___boxed(
    mut v_xs_267_: *mut crate::leanh::LeanObject,
    mut v_x_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Lean_RArray_ofArray___redArg___lam__0(v_xs_267_, v_x_268_);
    crate::leanh::lean_dec(v_x_268_);
    crate::leanh::lean_dec_ref(v_xs_267_);
    return v_res_269_;
}
pub unsafe fn l_Lean_RArray_ofArray___redArg(
    mut v_xs_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_xs_270_);
    v___f_271_ = crate::leanh::lean_alloc_closure(
        l_Lean_RArray_ofArray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_271_, 0, v_xs_270_);
    v___x_272_ = lean_array_get_size(v_xs_270_);
    crate::leanh::lean_dec_ref(v_xs_270_);
    v___x_273_ = l_Lean_RArray_ofFn___redArg(v___x_272_, v___f_271_);
    return v___x_273_;
}
pub unsafe fn l_Lean_RArray_ofArray(
    mut v_00_u03b1_274_: *mut crate::leanh::LeanObject,
    mut v_xs_275_: *mut crate::leanh::LeanObject,
    mut v_h_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lean_RArray_ofArray___redArg(v_xs_275_);
    return v___x_277_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(
    mut v_a_278_: *mut crate::leanh::LeanObject,
    mut v_h__1_279_: *mut crate::leanh::LeanObject,
    mut v_h__2_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_278_) == 0 {
        let mut v_a_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_280_);
        v_a_281_ = crate::leanh::lean_ctor_get(v_a_278_, 0);
        crate::leanh::lean_inc(v_a_281_);
        crate::leanh::lean_dec_ref_known(v_a_278_, 1);
        v___x_282_ = crate::leanh::lean_apply_1(v_h__1_279_, v_a_281_);
        return v___x_282_;
    } else {
        let mut v_a_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_279_);
        v_a_283_ = crate::leanh::lean_ctor_get(v_a_278_, 0);
        crate::leanh::lean_inc(v_a_283_);
        v_a_284_ = crate::leanh::lean_ctor_get(v_a_278_, 1);
        crate::leanh::lean_inc_ref(v_a_284_);
        v_a_285_ = crate::leanh::lean_ctor_get(v_a_278_, 2);
        crate::leanh::lean_inc_ref(v_a_285_);
        crate::leanh::lean_dec_ref_known(v_a_278_, 3);
        v___x_286_ = crate::leanh::lean_apply_3(v_h__2_280_, v_a_283_, v_a_284_, v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(
    mut v_00_u03b1_287_: *mut crate::leanh::LeanObject,
    mut v_motive_288_: *mut crate::leanh::LeanObject,
    mut v_a_289_: *mut crate::leanh::LeanObject,
    mut v_h__1_290_: *mut crate::leanh::LeanObject,
    mut v_h__2_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_289_) == 0 {
        let mut v_a_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_291_);
        v_a_292_ = crate::leanh::lean_ctor_get(v_a_289_, 0);
        crate::leanh::lean_inc(v_a_292_);
        crate::leanh::lean_dec_ref_known(v_a_289_, 1);
        v___x_293_ = crate::leanh::lean_apply_1(v_h__1_290_, v_a_292_);
        return v___x_293_;
    } else {
        let mut v_a_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_290_);
        v_a_294_ = crate::leanh::lean_ctor_get(v_a_289_, 0);
        crate::leanh::lean_inc(v_a_294_);
        v_a_295_ = crate::leanh::lean_ctor_get(v_a_289_, 1);
        crate::leanh::lean_inc_ref(v_a_295_);
        v_a_296_ = crate::leanh::lean_ctor_get(v_a_289_, 2);
        crate::leanh::lean_inc_ref(v_a_296_);
        crate::leanh::lean_dec_ref_known(v_a_289_, 3);
        v___x_297_ = crate::leanh::lean_apply_3(v_h__2_291_, v_a_294_, v_a_295_, v_a_296_);
        return v___x_297_;
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
    mut v_ty_298_: *mut crate::leanh::LeanObject,
    mut v_f_299_: *mut crate::leanh::LeanObject,
    mut v_leaf_300_: *mut crate::leanh::LeanObject,
    mut v_branch_301_: *mut crate::leanh::LeanObject,
    mut v_a_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_307_: u8 = 0;
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_313_: u8 = 0;
    let mut v_a_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_323_: u8 = 0;
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_302_) == 0 {
                    crate::leanh::lean_dec_ref(v_branch_301_);
                    v_a_304_ = crate::leanh::lean_ctor_get(v_a_302_, 0);
                    v_isSharedCheck_313_ = (!crate::leanh::lean_is_exclusive(v_a_302_)) as u8;
                    if v_isSharedCheck_313_ == 0 {
                        v___x_306_ = v_a_302_;
                        v_isShared_307_ = v_isSharedCheck_313_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_304_);
                        crate::leanh::lean_dec(v_a_302_);
                        v___x_306_ = crate::leanh::lean_box(0);
                        v_isShared_307_ = v_isSharedCheck_313_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_314_ = crate::leanh::lean_ctor_get(v_a_302_, 0);
                    crate::leanh::lean_inc(v_a_314_);
                    v_a_315_ = crate::leanh::lean_ctor_get(v_a_302_, 1);
                    crate::leanh::lean_inc_ref(v_a_315_);
                    v_a_316_ = crate::leanh::lean_ctor_get(v_a_302_, 2);
                    crate::leanh::lean_inc_ref(v_a_316_);
                    crate::leanh::lean_dec_ref_known(v_a_302_, 3);
                    crate::leanh::lean_inc_ref_n(v_branch_301_, 2);
                    crate::leanh::lean_inc_ref(v_leaf_300_);
                    crate::leanh::lean_inc_ref(v_f_299_);
                    crate::leanh::lean_inc_ref_n(v_ty_298_, 2);
                    v___x_317_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
                        v_ty_298_,
                        v_f_299_,
                        v_leaf_300_,
                        v_branch_301_,
                        v_a_315_,
                    );
                    v_a_318_ = crate::leanh::lean_ctor_get(v___x_317_, 0);
                    crate::leanh::lean_inc(v_a_318_);
                    crate::leanh::lean_dec_ref(v___x_317_);
                    v___x_319_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
                        v_ty_298_,
                        v_f_299_,
                        v_leaf_300_,
                        v_branch_301_,
                        v_a_316_,
                    );
                    v_a_320_ = crate::leanh::lean_ctor_get(v___x_319_, 0);
                    v_isSharedCheck_329_ = (!crate::leanh::lean_is_exclusive(v___x_319_)) as u8;
                    if v_isSharedCheck_329_ == 0 {
                        v___x_322_ = v___x_319_;
                        v_isShared_323_ = v_isSharedCheck_329_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_320_);
                        crate::leanh::lean_dec(v___x_319_);
                        v___x_322_ = crate::leanh::lean_box(0);
                        v_isShared_323_ = v_isSharedCheck_329_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_308_ = crate::leanh::lean_apply_1(v_f_299_, v_a_304_);
                v___x_309_ = l_Lean_mkAppB(v_leaf_300_, v_ty_298_, v___x_308_);
                if v_isShared_307_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_306_, 0, v___x_309_);
                    v___x_311_ = v___x_306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
                    v___x_311_ = v_reuseFailAlloc_312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_311_;
            }
            3 => {
                v___x_324_ = l_Lean_mkRawNatLit(v_a_314_);
                v___x_325_ =
                    l_Lean_mkApp4(v_branch_301_, v_ty_298_, v___x_324_, v_a_318_, v_a_320_);
                if v_isShared_323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_325_);
                    v___x_327_ = v___x_322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
                    v___x_327_ = v_reuseFailAlloc_328_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg___boxed(
    mut v_ty_330_: *mut crate::leanh::LeanObject,
    mut v_f_331_: *mut crate::leanh::LeanObject,
    mut v_leaf_332_: *mut crate::leanh::LeanObject,
    mut v_branch_333_: *mut crate::leanh::LeanObject,
    mut v_a_334_: *mut crate::leanh::LeanObject,
    mut v_a_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_336_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
        v_ty_330_,
        v_f_331_,
        v_leaf_332_,
        v_branch_333_,
        v_a_334_,
    );
    return v_res_336_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(
    mut v_00_u03b1_337_: *mut crate::leanh::LeanObject,
    mut v_ty_338_: *mut crate::leanh::LeanObject,
    mut v_f_339_: *mut crate::leanh::LeanObject,
    mut v_leaf_340_: *mut crate::leanh::LeanObject,
    mut v_branch_341_: *mut crate::leanh::LeanObject,
    mut v_a_342_: *mut crate::leanh::LeanObject,
    mut v_a_343_: *mut crate::leanh::LeanObject,
    mut v_a_344_: *mut crate::leanh::LeanObject,
    mut v_a_345_: *mut crate::leanh::LeanObject,
    mut v_a_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_348_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
        v_ty_338_,
        v_f_339_,
        v_leaf_340_,
        v_branch_341_,
        v_a_342_,
    );
    return v___x_348_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___boxed(
    mut v_00_u03b1_349_: *mut crate::leanh::LeanObject,
    mut v_ty_350_: *mut crate::leanh::LeanObject,
    mut v_f_351_: *mut crate::leanh::LeanObject,
    mut v_leaf_352_: *mut crate::leanh::LeanObject,
    mut v_branch_353_: *mut crate::leanh::LeanObject,
    mut v_a_354_: *mut crate::leanh::LeanObject,
    mut v_a_355_: *mut crate::leanh::LeanObject,
    mut v_a_356_: *mut crate::leanh::LeanObject,
    mut v_a_357_: *mut crate::leanh::LeanObject,
    mut v_a_358_: *mut crate::leanh::LeanObject,
    mut v_a_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go(
        v_00_u03b1_349_,
        v_ty_350_,
        v_f_351_,
        v_leaf_352_,
        v_branch_353_,
        v_a_354_,
        v_a_355_,
        v_a_356_,
        v_a_357_,
        v_a_358_,
    );
    crate::leanh::lean_dec(v_a_358_);
    crate::leanh::lean_dec_ref(v_a_357_);
    crate::leanh::lean_dec(v_a_356_);
    crate::leanh::lean_dec_ref(v_a_355_);
    return v_res_360_;
}
pub unsafe fn l_Lean_RArray_toExpr___redArg(
    mut v_ty_373_: *mut crate::leanh::LeanObject,
    mut v_f_374_: *mut crate::leanh::LeanObject,
    mut v_a_375_: *mut crate::leanh::LeanObject,
    mut v_a_376_: *mut crate::leanh::LeanObject,
    mut v_a_377_: *mut crate::leanh::LeanObject,
    mut v_a_378_: *mut crate::leanh::LeanObject,
    mut v_a_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_393_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_ty_373_);
                v___x_381_ =
                    l_Lean_Meta_getDecLevel(v_ty_373_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
                if crate::leanh::lean_obj_tag(v___x_381_) == 0 {
                    v_a_382_ = crate::leanh::lean_ctor_get(v___x_381_, 0);
                    crate::leanh::lean_inc(v_a_382_);
                    crate::leanh::lean_dec_ref_known(v___x_381_, 1);
                    v___x_383_ = l_Lean_RArray_toExpr___redArg___closed__3;
                    v___x_384_ = crate::leanh::lean_box(0);
                    v___x_385_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_385_, 0, v_a_382_);
                    crate::leanh::lean_ctor_set(v___x_385_, 1, v___x_384_);
                    crate::leanh::lean_inc_ref(v___x_385_);
                    v___x_386_ = l_Lean_mkConst(v___x_383_, v___x_385_);
                    v___x_387_ = l_Lean_RArray_toExpr___redArg___closed__5;
                    v___x_388_ = l_Lean_mkConst(v___x_387_, v___x_385_);
                    v___x_389_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
                        v_ty_373_, v_f_374_, v___x_386_, v___x_388_, v_a_375_,
                    );
                    return v___x_389_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_375_);
                    crate::leanh::lean_dec_ref(v_f_374_);
                    crate::leanh::lean_dec_ref(v_ty_373_);
                    v_a_390_ = crate::leanh::lean_ctor_get(v___x_381_, 0);
                    v_isSharedCheck_397_ = (!crate::leanh::lean_is_exclusive(v___x_381_)) as u8;
                    if v_isSharedCheck_397_ == 0 {
                        v___x_392_ = v___x_381_;
                        v_isShared_393_ = v_isSharedCheck_397_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_390_);
                        crate::leanh::lean_dec(v___x_381_);
                        v___x_392_ = crate::leanh::lean_box(0);
                        v_isShared_393_ = v_isSharedCheck_397_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_393_ == 0 {
                    v___x_395_ = v___x_392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
                    v___x_395_ = v_reuseFailAlloc_396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RArray_toExpr___redArg___boxed(
    mut v_ty_398_: *mut crate::leanh::LeanObject,
    mut v_f_399_: *mut crate::leanh::LeanObject,
    mut v_a_400_: *mut crate::leanh::LeanObject,
    mut v_a_401_: *mut crate::leanh::LeanObject,
    mut v_a_402_: *mut crate::leanh::LeanObject,
    mut v_a_403_: *mut crate::leanh::LeanObject,
    mut v_a_404_: *mut crate::leanh::LeanObject,
    mut v_a_405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_406_ = l_Lean_RArray_toExpr___redArg(
        v_ty_398_, v_f_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_,
    );
    crate::leanh::lean_dec(v_a_404_);
    crate::leanh::lean_dec_ref(v_a_403_);
    crate::leanh::lean_dec(v_a_402_);
    crate::leanh::lean_dec_ref(v_a_401_);
    return v_res_406_;
}
pub unsafe fn l_Lean_RArray_toExpr(
    mut v_00_u03b1_407_: *mut crate::leanh::LeanObject,
    mut v_ty_408_: *mut crate::leanh::LeanObject,
    mut v_f_409_: *mut crate::leanh::LeanObject,
    mut v_a_410_: *mut crate::leanh::LeanObject,
    mut v_a_411_: *mut crate::leanh::LeanObject,
    mut v_a_412_: *mut crate::leanh::LeanObject,
    mut v_a_413_: *mut crate::leanh::LeanObject,
    mut v_a_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_RArray_toExpr___redArg(
        v_ty_408_, v_f_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lean_RArray_toExpr___boxed(
    mut v_00_u03b1_417_: *mut crate::leanh::LeanObject,
    mut v_ty_418_: *mut crate::leanh::LeanObject,
    mut v_f_419_: *mut crate::leanh::LeanObject,
    mut v_a_420_: *mut crate::leanh::LeanObject,
    mut v_a_421_: *mut crate::leanh::LeanObject,
    mut v_a_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_426_ = l_Lean_RArray_toExpr(
        v_00_u03b1_417_,
        v_ty_418_,
        v_f_419_,
        v_a_420_,
        v_a_421_,
        v_a_422_,
        v_a_423_,
        v_a_424_,
    );
    crate::leanh::lean_dec(v_a_424_);
    crate::leanh::lean_dec_ref(v_a_423_);
    crate::leanh::lean_dec(v_a_422_);
    crate::leanh::lean_dec_ref(v_a_421_);
    return v_res_426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_RArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_RArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_RArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_RArray(builtin);
}
