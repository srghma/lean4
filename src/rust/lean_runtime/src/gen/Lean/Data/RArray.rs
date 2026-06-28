// Lean compiler output
// Module: Lean.Data.RArray
// Imports: Lean.Meta.DecLevel Init.Data.RArray Init.Omega
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr3;
use crate::r#gen::Lean::Expr::{l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkRawNatLit};
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, l_Lean_Meta_getDecLevel, runtime_initialize_Lean_Meta_DecLevel,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_RArray_toExpr___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_RArray_toExpr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_RArray_toExpr___redArg___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_RArray_toExpr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_RArray_toExpr___redArg___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_RArray_toExpr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__2_value) as *mut LeanObject;
static l_Lean_RArray_toExpr___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_RArray_toExpr___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__3_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__1_value) as *mut LeanObject,
        6242463428107210078 as *mut LeanObject,
    ],
};
pub static l_Lean_RArray_toExpr___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__3_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__2_value) as *mut LeanObject,
        803888951960056121 as *mut LeanObject,
    ],
};
static mut l_Lean_RArray_toExpr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_RArray_toExpr___redArg___closed__4_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_RArray_toExpr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__4_value) as *mut LeanObject;
static l_Lean_RArray_toExpr___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_RArray_toExpr___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__5_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__1_value) as *mut LeanObject,
        6242463428107210078 as *mut LeanObject,
    ],
};
pub static l_Lean_RArray_toExpr___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__5_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__4_value) as *mut LeanObject,
        5673740600655488943 as *mut LeanObject,
    ],
};
static mut l_Lean_RArray_toExpr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_RArray_toExpr___redArg___closed__5_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
    mut v_f_214_: *mut LeanObject,
    mut v_lb_215_: *mut LeanObject,
    mut v_ub_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: u8 = 0;
    v___x_217_ = lean_unsigned_to_nat(1);
    v___x_218_ = lean_nat_add(v_lb_215_, v___x_217_);
    v___x_219_ = lean_nat_dec_eq(v___x_218_, v_ub_216_);
    lean_dec(v___x_218_);
    if v___x_219_ == 0 {
        let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
        let mut v_mid_221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
        v___x_220_ = lean_nat_add(v_lb_215_, v_ub_216_);
        v_mid_221_ = lean_nat_shiftr(v___x_220_, v___x_217_);
        lean_dec(v___x_220_);
        lean_inc(v_f_214_);
        v___x_222_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
            v_f_214_, v_lb_215_, v_mid_221_,
        );
        lean_inc(v_mid_221_);
        v___x_223_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
            v_f_214_, v_mid_221_, v_ub_216_,
        );
        v___x_224_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_224_, 0, v_mid_221_);
        lean_ctor_set(v___x_224_, 1, v___x_222_);
        lean_ctor_set(v___x_224_, 2, v___x_223_);
        return v___x_224_;
    } else {
        let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
        v___x_225_ = lean_apply_1(v_f_214_, v_lb_215_);
        v___x_226_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_226_, 0, v___x_225_);
        return v___x_226_;
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg___boxed(
    mut v_f_227_: *mut LeanObject,
    mut v_lb_228_: *mut LeanObject,
    mut v_ub_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_230_: *mut LeanObject = core::ptr::null_mut();
    v_res_230_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
        v_f_227_, v_lb_228_, v_ub_229_,
    );
    lean_dec(v_ub_229_);
    return v_res_230_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(
    mut v_00_u03b1_231_: *mut LeanObject,
    mut v_n_232_: *mut LeanObject,
    mut v_f_233_: *mut LeanObject,
    mut v_lb_234_: *mut LeanObject,
    mut v_ub_235_: *mut LeanObject,
    mut v_h1_236_: *mut LeanObject,
    mut v_h2_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    v___x_238_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
        v_f_233_, v_lb_234_, v_ub_235_,
    );
    return v___x_238_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___boxed(
    mut v_00_u03b1_239_: *mut LeanObject,
    mut v_n_240_: *mut LeanObject,
    mut v_f_241_: *mut LeanObject,
    mut v_lb_242_: *mut LeanObject,
    mut v_ub_243_: *mut LeanObject,
    mut v_h1_244_: *mut LeanObject,
    mut v_h2_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_246_: *mut LeanObject = core::ptr::null_mut();
    v_res_246_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go(
        v_00_u03b1_239_,
        v_n_240_,
        v_f_241_,
        v_lb_242_,
        v_ub_243_,
        v_h1_244_,
        v_h2_245_,
    );
    lean_dec(v_ub_243_);
    lean_dec(v_n_240_);
    return v_res_246_;
}
pub unsafe fn l_Lean_RArray_ofFn___redArg(
    mut v_n_247_: *mut LeanObject,
    mut v_f_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    v___x_249_ = lean_unsigned_to_nat(0);
    v___x_250_ = l___private_Lean_Data_RArray_0__Lean_RArray_ofFn_go___redArg(
        v_f_248_, v___x_249_, v_n_247_,
    );
    return v___x_250_;
}
pub unsafe fn l_Lean_RArray_ofFn___redArg___boxed(
    mut v_n_251_: *mut LeanObject,
    mut v_f_252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_253_: *mut LeanObject = core::ptr::null_mut();
    v_res_253_ = l_Lean_RArray_ofFn___redArg(v_n_251_, v_f_252_);
    lean_dec(v_n_251_);
    return v_res_253_;
}
pub unsafe fn l_Lean_RArray_ofFn(
    mut v_00_u03b1_254_: *mut LeanObject,
    mut v_n_255_: *mut LeanObject,
    mut v_f_256_: *mut LeanObject,
    mut v_h_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    v___x_258_ = l_Lean_RArray_ofFn___redArg(v_n_255_, v_f_256_);
    return v___x_258_;
}
pub unsafe fn l_Lean_RArray_ofFn___boxed(
    mut v_00_u03b1_259_: *mut LeanObject,
    mut v_n_260_: *mut LeanObject,
    mut v_f_261_: *mut LeanObject,
    mut v_h_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_263_: *mut LeanObject = core::ptr::null_mut();
    v_res_263_ = l_Lean_RArray_ofFn(v_00_u03b1_259_, v_n_260_, v_f_261_, v_h_262_);
    lean_dec(v_n_260_);
    return v_res_263_;
}
pub unsafe fn l_Lean_RArray_ofArray___redArg___lam__0(
    mut v_xs_264_: *mut LeanObject,
    mut v_x_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = lean_array_fget_borrowed(v_xs_264_, v_x_265_);
    lean_inc(v___x_266_);
    return v___x_266_;
}
pub unsafe fn l_Lean_RArray_ofArray___redArg___lam__0___boxed(
    mut v_xs_267_: *mut LeanObject,
    mut v_x_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Lean_RArray_ofArray___redArg___lam__0(v_xs_267_, v_x_268_);
    lean_dec(v_x_268_);
    lean_dec_ref(v_xs_267_);
    return v_res_269_;
}
pub unsafe fn l_Lean_RArray_ofArray___redArg(mut v_xs_270_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_xs_270_);
    v___f_271_ = lean_alloc_closure(
        l_Lean_RArray_ofArray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_271_, 0, v_xs_270_);
    v___x_272_ = lean_array_get_size(v_xs_270_);
    lean_dec_ref(v_xs_270_);
    v___x_273_ = l_Lean_RArray_ofFn___redArg(v___x_272_, v___f_271_);
    return v___x_273_;
}
pub unsafe fn l_Lean_RArray_ofArray(
    mut v_00_u03b1_274_: *mut LeanObject,
    mut v_xs_275_: *mut LeanObject,
    mut v_h_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lean_RArray_ofArray___redArg(v_xs_275_);
    return v___x_277_;
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(
    mut v_a_278_: *mut LeanObject,
    mut v_h__1_279_: *mut LeanObject,
    mut v_h__2_280_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_278_) == 0 {
        let mut v_a_281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_280_);
        v_a_281_ = lean_ctor_get(v_a_278_, 0);
        lean_inc(v_a_281_);
        lean_dec_ref_known(v_a_278_, 1);
        v___x_282_ = lean_apply_1(v_h__1_279_, v_a_281_);
        return v___x_282_;
    } else {
        let mut v_a_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_279_);
        v_a_283_ = lean_ctor_get(v_a_278_, 0);
        lean_inc(v_a_283_);
        v_a_284_ = lean_ctor_get(v_a_278_, 1);
        lean_inc_ref(v_a_284_);
        v_a_285_ = lean_ctor_get(v_a_278_, 2);
        lean_inc_ref(v_a_285_);
        lean_dec_ref_known(v_a_278_, 3);
        v___x_286_ = lean_apply_3(v_h__2_280_, v_a_283_, v_a_284_, v_a_285_);
        return v___x_286_;
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(
    mut v_00_u03b1_287_: *mut LeanObject,
    mut v_motive_288_: *mut LeanObject,
    mut v_a_289_: *mut LeanObject,
    mut v_h__1_290_: *mut LeanObject,
    mut v_h__2_291_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_289_) == 0 {
        let mut v_a_292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_291_);
        v_a_292_ = lean_ctor_get(v_a_289_, 0);
        lean_inc(v_a_292_);
        lean_dec_ref_known(v_a_289_, 1);
        v___x_293_ = lean_apply_1(v_h__1_290_, v_a_292_);
        return v___x_293_;
    } else {
        let mut v_a_294_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_295_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_290_);
        v_a_294_ = lean_ctor_get(v_a_289_, 0);
        lean_inc(v_a_294_);
        v_a_295_ = lean_ctor_get(v_a_289_, 1);
        lean_inc_ref(v_a_295_);
        v_a_296_ = lean_ctor_get(v_a_289_, 2);
        lean_inc_ref(v_a_296_);
        lean_dec_ref_known(v_a_289_, 3);
        v___x_297_ = lean_apply_3(v_h__2_291_, v_a_294_, v_a_295_, v_a_296_);
        return v___x_297_;
    }
}
pub unsafe fn l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
    mut v_ty_298_: *mut LeanObject,
    mut v_f_299_: *mut LeanObject,
    mut v_leaf_300_: *mut LeanObject,
    mut v_branch_301_: *mut LeanObject,
    mut v_a_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_307_: u8 = 0;
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_313_: u8 = 0;
    let mut v_a_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_323_: u8 = 0;
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_302_) == 0 {
                    lean_dec_ref(v_branch_301_);
                    v_a_304_ = lean_ctor_get(v_a_302_, 0);
                    v_isSharedCheck_313_ = (!lean_is_exclusive(v_a_302_)) as u8;
                    if v_isSharedCheck_313_ == 0 {
                        v___x_306_ = v_a_302_;
                        v_isShared_307_ = v_isSharedCheck_313_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_304_);
                        lean_dec(v_a_302_);
                        v___x_306_ = lean_box(0);
                        v_isShared_307_ = v_isSharedCheck_313_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_314_ = lean_ctor_get(v_a_302_, 0);
                    lean_inc(v_a_314_);
                    v_a_315_ = lean_ctor_get(v_a_302_, 1);
                    lean_inc_ref(v_a_315_);
                    v_a_316_ = lean_ctor_get(v_a_302_, 2);
                    lean_inc_ref(v_a_316_);
                    lean_dec_ref_known(v_a_302_, 3);
                    lean_inc_ref_n(v_branch_301_, 2);
                    lean_inc_ref(v_leaf_300_);
                    lean_inc_ref(v_f_299_);
                    lean_inc_ref_n(v_ty_298_, 2);
                    v___x_317_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
                        v_ty_298_,
                        v_f_299_,
                        v_leaf_300_,
                        v_branch_301_,
                        v_a_315_,
                    );
                    v_a_318_ = lean_ctor_get(v___x_317_, 0);
                    lean_inc(v_a_318_);
                    lean_dec_ref(v___x_317_);
                    v___x_319_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
                        v_ty_298_,
                        v_f_299_,
                        v_leaf_300_,
                        v_branch_301_,
                        v_a_316_,
                    );
                    v_a_320_ = lean_ctor_get(v___x_319_, 0);
                    v_isSharedCheck_329_ = (!lean_is_exclusive(v___x_319_)) as u8;
                    if v_isSharedCheck_329_ == 0 {
                        v___x_322_ = v___x_319_;
                        v_isShared_323_ = v_isSharedCheck_329_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_320_);
                        lean_dec(v___x_319_);
                        v___x_322_ = lean_box(0);
                        v_isShared_323_ = v_isSharedCheck_329_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_308_ = lean_apply_1(v_f_299_, v_a_304_);
                v___x_309_ = l_Lean_mkAppB(v_leaf_300_, v_ty_298_, v___x_308_);
                if v_isShared_307_ == 0 {
                    lean_ctor_set(v___x_306_, 0, v___x_309_);
                    v___x_311_ = v___x_306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
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
                    lean_ctor_set(v___x_322_, 0, v___x_325_);
                    v___x_327_ = v___x_322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
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
    mut v_ty_330_: *mut LeanObject,
    mut v_f_331_: *mut LeanObject,
    mut v_leaf_332_: *mut LeanObject,
    mut v_branch_333_: *mut LeanObject,
    mut v_a_334_: *mut LeanObject,
    mut v_a_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_336_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_337_: *mut LeanObject,
    mut v_ty_338_: *mut LeanObject,
    mut v_f_339_: *mut LeanObject,
    mut v_leaf_340_: *mut LeanObject,
    mut v_branch_341_: *mut LeanObject,
    mut v_a_342_: *mut LeanObject,
    mut v_a_343_: *mut LeanObject,
    mut v_a_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
    mut v_a_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_349_: *mut LeanObject,
    mut v_ty_350_: *mut LeanObject,
    mut v_f_351_: *mut LeanObject,
    mut v_leaf_352_: *mut LeanObject,
    mut v_branch_353_: *mut LeanObject,
    mut v_a_354_: *mut LeanObject,
    mut v_a_355_: *mut LeanObject,
    mut v_a_356_: *mut LeanObject,
    mut v_a_357_: *mut LeanObject,
    mut v_a_358_: *mut LeanObject,
    mut v_a_359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_360_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_358_);
    lean_dec_ref(v_a_357_);
    lean_dec(v_a_356_);
    lean_dec_ref(v_a_355_);
    return v_res_360_;
}
pub unsafe fn l_Lean_RArray_toExpr___redArg(
    mut v_ty_373_: *mut LeanObject,
    mut v_f_374_: *mut LeanObject,
    mut v_a_375_: *mut LeanObject,
    mut v_a_376_: *mut LeanObject,
    mut v_a_377_: *mut LeanObject,
    mut v_a_378_: *mut LeanObject,
    mut v_a_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_393_: u8 = 0;
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_ty_373_);
                v___x_381_ =
                    l_Lean_Meta_getDecLevel(v_ty_373_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
                if lean_obj_tag(v___x_381_) == 0 {
                    v_a_382_ = lean_ctor_get(v___x_381_, 0);
                    lean_inc(v_a_382_);
                    lean_dec_ref_known(v___x_381_, 1);
                    v___x_383_ = l_Lean_RArray_toExpr___redArg___closed__3;
                    v___x_384_ = lean_box(0);
                    v___x_385_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_385_, 0, v_a_382_);
                    lean_ctor_set(v___x_385_, 1, v___x_384_);
                    lean_inc_ref(v___x_385_);
                    v___x_386_ = l_Lean_mkConst(v___x_383_, v___x_385_);
                    v___x_387_ = l_Lean_RArray_toExpr___redArg___closed__5;
                    v___x_388_ = l_Lean_mkConst(v___x_387_, v___x_385_);
                    v___x_389_ = l___private_Lean_Data_RArray_0__Lean_RArray_toExpr_go___redArg(
                        v_ty_373_, v_f_374_, v___x_386_, v___x_388_, v_a_375_,
                    );
                    return v___x_389_;
                } else {
                    lean_dec_ref(v_a_375_);
                    lean_dec_ref(v_f_374_);
                    lean_dec_ref(v_ty_373_);
                    v_a_390_ = lean_ctor_get(v___x_381_, 0);
                    v_isSharedCheck_397_ = (!lean_is_exclusive(v___x_381_)) as u8;
                    if v_isSharedCheck_397_ == 0 {
                        v___x_392_ = v___x_381_;
                        v_isShared_393_ = v_isSharedCheck_397_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_390_);
                        lean_dec(v___x_381_);
                        v___x_392_ = lean_box(0);
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
                    v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
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
    mut v_ty_398_: *mut LeanObject,
    mut v_f_399_: *mut LeanObject,
    mut v_a_400_: *mut LeanObject,
    mut v_a_401_: *mut LeanObject,
    mut v_a_402_: *mut LeanObject,
    mut v_a_403_: *mut LeanObject,
    mut v_a_404_: *mut LeanObject,
    mut v_a_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_406_: *mut LeanObject = core::ptr::null_mut();
    v_res_406_ = l_Lean_RArray_toExpr___redArg(
        v_ty_398_, v_f_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_,
    );
    lean_dec(v_a_404_);
    lean_dec_ref(v_a_403_);
    lean_dec(v_a_402_);
    lean_dec_ref(v_a_401_);
    return v_res_406_;
}
pub unsafe fn l_Lean_RArray_toExpr(
    mut v_00_u03b1_407_: *mut LeanObject,
    mut v_ty_408_: *mut LeanObject,
    mut v_f_409_: *mut LeanObject,
    mut v_a_410_: *mut LeanObject,
    mut v_a_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v_a_413_: *mut LeanObject,
    mut v_a_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = l_Lean_RArray_toExpr___redArg(
        v_ty_408_, v_f_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_,
    );
    return v___x_416_;
}
pub unsafe fn l_Lean_RArray_toExpr___boxed(
    mut v_00_u03b1_417_: *mut LeanObject,
    mut v_ty_418_: *mut LeanObject,
    mut v_f_419_: *mut LeanObject,
    mut v_a_420_: *mut LeanObject,
    mut v_a_421_: *mut LeanObject,
    mut v_a_422_: *mut LeanObject,
    mut v_a_423_: *mut LeanObject,
    mut v_a_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_426_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_424_);
    lean_dec_ref(v_a_423_);
    lean_dec(v_a_422_);
    lean_dec_ref(v_a_421_);
    return v_res_426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_RArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_RArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_RArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_RArray(builtin);
}
