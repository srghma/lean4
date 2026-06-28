// Lean compiler output
// Module: Lean.Meta.Sym.Offset
// Imports: Lean.Meta.Sym.LitValues
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Meta::Sym::LitValues::{
    initialize_Lean_Meta_Sym_LitValues, l_Lean_Meta_Sym_getNatValue_x3f,
    runtime_initialize_Lean_Meta_Sym_LitValues,
};
use crate::lean_imports_rs::Init::Prelude::{lean_name_eq, lean_nat_add};
pub static l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedOffset_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 117, 99, 99, 0],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_isOffset_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16112798088292836701 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [104, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [72, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_isOffset_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
            10393083817453678557 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__4_value)
                as *mut crate::leanh::LeanObject,
            10680564408669940870 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_isOffset_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [79, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Sym_isOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_isOffset___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [111, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Sym_isOffset___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_isOffset___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17636616155771105671 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_isOffset___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15578568367168711682 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_isOffset___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_isOffset___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Offset_ctorIdx(
    mut v_x_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_246_) == 0 {
        let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_247_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_247_;
    } else {
        let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_248_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_248_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Offset_ctorIdx___boxed(
    mut v_x_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_250_ = l_Lean_Meta_Sym_Offset_ctorIdx(v_x_249_);
    crate::leanh::lean_dec_ref(v_x_249_);
    return v_res_250_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_ctorElim___redArg(
    mut v_t_251_: *mut crate::leanh::LeanObject,
    mut v_k_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_251_) == 0 {
        let mut v_k_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_253_ = crate::leanh::lean_ctor_get(v_t_251_, 0);
        crate::leanh::lean_inc(v_k_253_);
        crate::leanh::lean_dec_ref_known(v_t_251_, 1);
        v___x_254_ = crate::leanh::lean_apply_1(v_k_252_, v_k_253_);
        return v___x_254_;
    } else {
        let mut v_e_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_255_ = crate::leanh::lean_ctor_get(v_t_251_, 0);
        crate::leanh::lean_inc_ref(v_e_255_);
        v_k_256_ = crate::leanh::lean_ctor_get(v_t_251_, 1);
        crate::leanh::lean_inc(v_k_256_);
        crate::leanh::lean_dec_ref_known(v_t_251_, 2);
        v___x_257_ = crate::leanh::lean_apply_2(v_k_252_, v_e_255_, v_k_256_);
        return v___x_257_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Offset_ctorElim(
    mut v_motive_258_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_259_: *mut crate::leanh::LeanObject,
    mut v_t_260_: *mut crate::leanh::LeanObject,
    mut v_h_261_: *mut crate::leanh::LeanObject,
    mut v_k_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_260_, v_k_262_);
    return v___x_263_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_ctorElim___boxed(
    mut v_motive_264_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_265_: *mut crate::leanh::LeanObject,
    mut v_t_266_: *mut crate::leanh::LeanObject,
    mut v_h_267_: *mut crate::leanh::LeanObject,
    mut v_k_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Lean_Meta_Sym_Offset_ctorElim(
        v_motive_264_,
        v_ctorIdx_265_,
        v_t_266_,
        v_h_267_,
        v_k_268_,
    );
    crate::leanh::lean_dec(v_ctorIdx_265_);
    return v_res_269_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_num_elim___redArg(
    mut v_t_270_: *mut crate::leanh::LeanObject,
    mut v_num_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_270_, v_num_271_);
    return v___x_272_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_num_elim(
    mut v_motive_273_: *mut crate::leanh::LeanObject,
    mut v_t_274_: *mut crate::leanh::LeanObject,
    mut v_h_275_: *mut crate::leanh::LeanObject,
    mut v_num_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_277_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_274_, v_num_276_);
    return v___x_277_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_add_elim___redArg(
    mut v_t_278_: *mut crate::leanh::LeanObject,
    mut v_add_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_278_, v_add_279_);
    return v___x_280_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_add_elim(
    mut v_motive_281_: *mut crate::leanh::LeanObject,
    mut v_t_282_: *mut crate::leanh::LeanObject,
    mut v_h_283_: *mut crate::leanh::LeanObject,
    mut v_add_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_282_, v_add_284_);
    return v___x_285_;
}
pub unsafe fn l_Lean_Meta_Sym_Offset_inc(
    mut v_x_290_: *mut crate::leanh::LeanObject,
    mut v_x_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut v_e_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_305_: u8 = 0;
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_290_) == 0 {
                    v_k_292_ = crate::leanh::lean_ctor_get(v_x_290_, 0);
                    v_isSharedCheck_300_ = (!crate::leanh::lean_is_exclusive(v_x_290_)) as u8;
                    if v_isSharedCheck_300_ == 0 {
                        v___x_294_ = v_x_290_;
                        v_isShared_295_ = v_isSharedCheck_300_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_292_);
                        crate::leanh::lean_dec(v_x_290_);
                        v___x_294_ = crate::leanh::lean_box(0);
                        v_isShared_295_ = v_isSharedCheck_300_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_301_ = crate::leanh::lean_ctor_get(v_x_290_, 0);
                    v_k_302_ = crate::leanh::lean_ctor_get(v_x_290_, 1);
                    v_isSharedCheck_310_ = (!crate::leanh::lean_is_exclusive(v_x_290_)) as u8;
                    if v_isSharedCheck_310_ == 0 {
                        v___x_304_ = v_x_290_;
                        v_isShared_305_ = v_isSharedCheck_310_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_302_);
                        crate::leanh::lean_inc(v_e_301_);
                        crate::leanh::lean_dec(v_x_290_);
                        v___x_304_ = crate::leanh::lean_box(0);
                        v_isShared_305_ = v_isSharedCheck_310_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_296_ = lean_nat_add(v_k_292_, v_x_291_);
                crate::leanh::lean_dec(v_k_292_);
                if v_isShared_295_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_294_, 0, v___x_296_);
                    v___x_298_ = v___x_294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
                    v___x_298_ = v_reuseFailAlloc_299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_298_;
            }
            3 => {
                v___x_306_ = lean_nat_add(v_k_302_, v_x_291_);
                crate::leanh::lean_dec(v_k_302_);
                if v_isShared_305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_304_, 1, v___x_306_);
                    v___x_308_ = v___x_304_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_309_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_309_, 0, v_e_301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_306_);
                    v___x_308_ = v_reuseFailAlloc_309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Offset_inc___boxed(
    mut v_x_311_: *mut crate::leanh::LeanObject,
    mut v_x_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Lean_Meta_Sym_Offset_inc(v_x_311_, v_x_312_);
    crate::leanh::lean_dec(v_x_312_);
    return v_res_313_;
}
pub unsafe fn l_Lean_Meta_Sym_isOffset_x3f(
    mut v_e_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: u8 = 0;
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: u8 = 0;
    let mut v___x_334_: u8 = 0;
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: u8 = 0;
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: u8 = 0;
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: u8 = 0;
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: u8 = 0;
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: u8 = 0;
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: u8 = 0;
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_362_: u8 = 0;
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_368_: u8 = 0;
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_327_ = l_Lean_Expr_cleanupAnnotations(v_e_326_);
                v___x_328_ = l_Lean_Expr_isApp(v___x_327_);
                if v___x_328_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_327_);
                    v___x_329_ = crate::leanh::lean_box(0);
                    return v___x_329_;
                } else {
                    v_arg_330_ = crate::leanh::lean_ctor_get(v___x_327_, 1);
                    crate::leanh::lean_inc_ref(v_arg_330_);
                    v___x_331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
                    v___x_332_ = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
                    v___x_333_ = l_Lean_Expr_isConstOf(v___x_331_, v___x_332_);
                    if v___x_333_ == 0 {
                        v___x_334_ = l_Lean_Expr_isApp(v___x_331_);
                        if v___x_334_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_331_);
                            crate::leanh::lean_dec_ref(v_arg_330_);
                            v___x_335_ = crate::leanh::lean_box(0);
                            return v___x_335_;
                        } else {
                            v_arg_336_ = crate::leanh::lean_ctor_get(v___x_331_, 1);
                            crate::leanh::lean_inc_ref(v_arg_336_);
                            v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
                            v___x_338_ = l_Lean_Expr_isApp(v___x_337_);
                            if v___x_338_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_337_);
                                crate::leanh::lean_dec_ref(v_arg_336_);
                                crate::leanh::lean_dec_ref(v_arg_330_);
                                v___x_339_ = crate::leanh::lean_box(0);
                                return v___x_339_;
                            } else {
                                v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
                                v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
                                if v___x_341_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_340_);
                                    crate::leanh::lean_dec_ref(v_arg_336_);
                                    crate::leanh::lean_dec_ref(v_arg_330_);
                                    v___x_342_ = crate::leanh::lean_box(0);
                                    return v___x_342_;
                                } else {
                                    v___x_343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
                                    v___x_344_ = l_Lean_Expr_isApp(v___x_343_);
                                    if v___x_344_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_343_);
                                        crate::leanh::lean_dec_ref(v_arg_336_);
                                        crate::leanh::lean_dec_ref(v_arg_330_);
                                        v___x_345_ = crate::leanh::lean_box(0);
                                        return v___x_345_;
                                    } else {
                                        v___x_346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_343_);
                                        v___x_347_ = l_Lean_Expr_isApp(v___x_346_);
                                        if v___x_347_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_346_);
                                            crate::leanh::lean_dec_ref(v_arg_336_);
                                            crate::leanh::lean_dec_ref(v_arg_330_);
                                            v___x_348_ = crate::leanh::lean_box(0);
                                            return v___x_348_;
                                        } else {
                                            v_arg_349_ = crate::leanh::lean_ctor_get(v___x_346_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_349_);
                                            v___x_350_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_346_);
                                            v___x_351_ = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
                                            v___x_352_ =
                                                l_Lean_Expr_isConstOf(v___x_350_, v___x_351_);
                                            crate::leanh::lean_dec_ref(v___x_350_);
                                            if v___x_352_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_349_);
                                                crate::leanh::lean_dec_ref(v_arg_336_);
                                                crate::leanh::lean_dec_ref(v_arg_330_);
                                                v___x_353_ = crate::leanh::lean_box(0);
                                                return v___x_353_;
                                            } else {
                                                v___x_354_ =
                                                    l_Lean_Meta_Sym_isOffset_x3f___closed__6;
                                                v___x_355_ =
                                                    l_Lean_Expr_isConstOf(v_arg_349_, v___x_354_);
                                                crate::leanh::lean_dec_ref(v_arg_349_);
                                                if v___x_355_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_336_);
                                                    crate::leanh::lean_dec_ref(v_arg_330_);
                                                    v___x_356_ = crate::leanh::lean_box(0);
                                                    return v___x_356_;
                                                } else {
                                                    v___x_357_ =
                                                        l_Lean_Meta_Sym_getNatValue_x3f(v_arg_330_);
                                                    if crate::leanh::lean_obj_tag(v___x_357_) == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_336_);
                                                        v___x_358_ = crate::leanh::lean_box(0);
                                                        return v___x_358_;
                                                    } else {
                                                        v_val_359_ = crate::leanh::lean_ctor_get(
                                                            v___x_357_, 0,
                                                        );
                                                        v_isSharedCheck_368_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_357_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_368_ == 0 {
                                                            v___x_361_ = v___x_357_;
                                                            v_isShared_362_ = v_isSharedCheck_368_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_val_359_);
                                                            crate::leanh::lean_dec(v___x_357_);
                                                            v___x_361_ = crate::leanh::lean_box(0);
                                                            v_isShared_362_ = v_isSharedCheck_368_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_331_);
                        v___x_369_ =
                            l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(
                                v_arg_330_,
                            );
                        v___x_370_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_371_ = l_Lean_Meta_Sym_Offset_inc(v___x_369_, v___x_370_);
                        v___x_372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_372_, 0, v___x_371_);
                        return v___x_372_;
                    }
                }
            }
            1 => {
                v___x_363_ =
                    l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_336_);
                v___x_364_ = l_Lean_Meta_Sym_Offset_inc(v___x_363_, v_val_359_);
                crate::leanh::lean_dec(v_val_359_);
                if v_isShared_362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_361_, 0, v___x_364_);
                    v___x_366_ = v___x_361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
                    v___x_366_ = v_reuseFailAlloc_367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(
    mut v_e_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_373_);
    v___x_374_ = l_Lean_Meta_Sym_isOffset_x3f(v_e_373_);
    if crate::leanh::lean_obj_tag(v___x_374_) == 0 {
        let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_375_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_376_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_376_, 0, v_e_373_);
        crate::leanh::lean_ctor_set(v___x_376_, 1, v___x_375_);
        return v___x_376_;
    } else {
        let mut v_val_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_373_);
        v_val_377_ = crate::leanh::lean_ctor_get(v___x_374_, 0);
        crate::leanh::lean_inc(v_val_377_);
        crate::leanh::lean_dec_ref_known(v___x_374_, 1);
        return v_val_377_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_isOffset_x3f_x27(
    mut v_declName_378_: *mut crate::leanh::LeanObject,
    mut v_p_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_381_: u8 = 0;
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: u8 = 0;
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_384_ = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
                v___x_385_ = lean_name_eq(v_declName_378_, v___x_384_);
                if v___x_385_ == 0 {
                    v___x_386_ = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
                    v___x_387_ = lean_name_eq(v_declName_378_, v___x_386_);
                    v___y_381_ = v___x_387_;
                    state = 1;
                    continue;
                } else {
                    v___y_381_ = v___x_385_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_381_ == 0 {
                    crate::leanh::lean_dec_ref(v_p_379_);
                    v___x_382_ = crate::leanh::lean_box(0);
                    return v___x_382_;
                } else {
                    v___x_383_ = l_Lean_Meta_Sym_isOffset_x3f(v_p_379_);
                    return v___x_383_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(
    mut v_declName_388_: *mut crate::leanh::LeanObject,
    mut v_p_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Lean_Meta_Sym_isOffset_x3f_x27(v_declName_388_, v_p_389_);
    crate::leanh::lean_dec(v_declName_388_);
    return v_res_390_;
}
pub unsafe fn l_Lean_Meta_Sym_isOffset(mut v_e_396_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: u8 = 0;
    v___x_397_ = l_Lean_Expr_cleanupAnnotations(v_e_396_);
    v___x_398_ = l_Lean_Expr_isApp(v___x_397_);
    if v___x_398_ == 0 {
        crate::leanh::lean_dec_ref(v___x_397_);
        return v___x_398_;
    } else {
        let mut v_arg_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: u8 = 0;
        v_arg_399_ = crate::leanh::lean_ctor_get(v___x_397_, 1);
        crate::leanh::lean_inc_ref(v_arg_399_);
        v___x_400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_397_);
        v___x_401_ = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
        v___x_402_ = l_Lean_Expr_isConstOf(v___x_400_, v___x_401_);
        if v___x_402_ == 0 {
            let mut v___x_403_: u8 = 0;
            v___x_403_ = l_Lean_Expr_isApp(v___x_400_);
            if v___x_403_ == 0 {
                crate::leanh::lean_dec_ref(v___x_400_);
                crate::leanh::lean_dec_ref(v_arg_399_);
                return v___x_403_;
            } else {
                let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_405_: u8 = 0;
                v___x_404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
                v___x_405_ = l_Lean_Expr_isApp(v___x_404_);
                if v___x_405_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_404_);
                    crate::leanh::lean_dec_ref(v_arg_399_);
                    return v___x_405_;
                } else {
                    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_407_: u8 = 0;
                    v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_404_);
                    v___x_407_ = l_Lean_Expr_isApp(v___x_406_);
                    if v___x_407_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_406_);
                        crate::leanh::lean_dec_ref(v_arg_399_);
                        return v___x_407_;
                    } else {
                        let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_409_: u8 = 0;
                        v___x_408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_406_);
                        v___x_409_ = l_Lean_Expr_isApp(v___x_408_);
                        if v___x_409_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_408_);
                            crate::leanh::lean_dec_ref(v_arg_399_);
                            return v___x_409_;
                        } else {
                            let mut v___x_410_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_411_: u8 = 0;
                            v___x_410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_408_);
                            v___x_411_ = l_Lean_Expr_isApp(v___x_410_);
                            if v___x_411_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_410_);
                                crate::leanh::lean_dec_ref(v_arg_399_);
                                return v___x_411_;
                            } else {
                                let mut v_arg_412_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_413_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_414_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_415_: u8 = 0;
                                v_arg_412_ = crate::leanh::lean_ctor_get(v___x_410_, 1);
                                crate::leanh::lean_inc_ref(v_arg_412_);
                                v___x_413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_410_);
                                v___x_414_ = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
                                v___x_415_ = l_Lean_Expr_isConstOf(v___x_413_, v___x_414_);
                                crate::leanh::lean_dec_ref(v___x_413_);
                                if v___x_415_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_412_);
                                    crate::leanh::lean_dec_ref(v_arg_399_);
                                    return v___x_415_;
                                } else {
                                    let mut v___x_416_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_417_: u8 = 0;
                                    v___x_416_ = l_Lean_Meta_Sym_isOffset_x3f___closed__6;
                                    v___x_417_ = l_Lean_Expr_isConstOf(v_arg_412_, v___x_416_);
                                    crate::leanh::lean_dec_ref(v_arg_412_);
                                    if v___x_417_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_399_);
                                        return v___x_417_;
                                    } else {
                                        let mut v___x_418_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_419_: u8 = 0;
                                        v___x_418_ = l_Lean_Expr_cleanupAnnotations(v_arg_399_);
                                        v___x_419_ = l_Lean_Expr_isApp(v___x_418_);
                                        if v___x_419_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_418_);
                                            return v___x_419_;
                                        } else {
                                            let mut v___x_420_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_421_: u8 = 0;
                                            v___x_420_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_418_);
                                            v___x_421_ = l_Lean_Expr_isApp(v___x_420_);
                                            if v___x_421_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_420_);
                                                return v___x_421_;
                                            } else {
                                                let mut v_arg_422_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_423_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_424_: u8 = 0;
                                                v_arg_422_ =
                                                    crate::leanh::lean_ctor_get(v___x_420_, 1);
                                                crate::leanh::lean_inc_ref(v_arg_422_);
                                                v___x_423_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_420_);
                                                v___x_424_ = l_Lean_Expr_isApp(v___x_423_);
                                                if v___x_424_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_423_);
                                                    crate::leanh::lean_dec_ref(v_arg_422_);
                                                    return v___x_424_;
                                                } else {
                                                    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_427_: u8 = 0;
                                                    v___x_425_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_423_,
                                                    );
                                                    v___x_426_ =
                                                        l_Lean_Meta_Sym_isOffset___closed__2;
                                                    v___x_427_ = l_Lean_Expr_isConstOf(
                                                        v___x_425_, v___x_426_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_425_);
                                                    if v___x_427_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_422_);
                                                        return v___x_427_;
                                                    } else {
                                                        if crate::leanh::lean_obj_tag(v_arg_422_)
                                                            == 9
                                                        {
                                                            let mut v_a_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            v_a_428_ = crate::leanh::lean_ctor_get(
                                                                v_arg_422_, 0,
                                                            );
                                                            crate::leanh::lean_inc_ref(v_a_428_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_arg_422_, 1,
                                                            );
                                                            if crate::leanh::lean_obj_tag(v_a_428_)
                                                                == 0
                                                            {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_a_428_, 1,
                                                                );
                                                                return v___x_417_;
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_428_,
                                                                );
                                                                return v___x_402_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_422_);
                                                            return v___x_402_;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } else {
            crate::leanh::lean_dec_ref(v___x_400_);
            crate::leanh::lean_dec_ref(v_arg_399_);
            return v___x_402_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isOffset___boxed(
    mut v_e_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Lean_Meta_Sym_isOffset(v_e_429_);
    v_r_431_ = crate::leanh::lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn l_Lean_Meta_Sym_isOffset_x27(
    mut v_declName_432_: *mut crate::leanh::LeanObject,
    mut v_p_433_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_435_: u8 = 0;
    let mut v___x_436_: u8 = 0;
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_437_ = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
                v___x_438_ = lean_name_eq(v_declName_432_, v___x_437_);
                if v___x_438_ == 0 {
                    v___x_439_ = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
                    v___x_440_ = lean_name_eq(v_declName_432_, v___x_439_);
                    v___y_435_ = v___x_440_;
                    state = 1;
                    continue;
                } else {
                    v___y_435_ = v___x_438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_435_ == 0 {
                    crate::leanh::lean_dec_ref(v_p_433_);
                    return v___y_435_;
                } else {
                    v___x_436_ = l_Lean_Meta_Sym_isOffset(v_p_433_);
                    return v___x_436_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isOffset_x27___boxed(
    mut v_declName_441_: *mut crate::leanh::LeanObject,
    mut v_p_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_443_: u8 = 0;
    let mut v_r_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_441_, v_p_442_);
    crate::leanh::lean_dec(v_declName_441_);
    v_r_444_ = crate::leanh::lean_box((v_res_443_) as usize);
    return v_r_444_;
}
pub unsafe fn l_Lean_Meta_Sym_toOffset(
    mut v_e_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: u8 = 0;
    let mut v_arg_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    let mut v___x_458_: u8 = 0;
    let mut v_arg_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: u8 = 0;
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: u8 = 0;
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: u8 = 0;
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_483_: u8 = 0;
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_445_);
                v___x_452_ = l_Lean_Expr_cleanupAnnotations(v_e_445_);
                v___x_453_ = l_Lean_Expr_isApp(v___x_452_);
                if v___x_453_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_452_);
                    state = 1;
                    continue;
                } else {
                    v_arg_454_ = crate::leanh::lean_ctor_get(v___x_452_, 1);
                    crate::leanh::lean_inc_ref(v_arg_454_);
                    v___x_455_ = l_Lean_Expr_appFnCleanup___redArg(v___x_452_);
                    v___x_456_ = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
                    v___x_457_ = l_Lean_Expr_isConstOf(v___x_455_, v___x_456_);
                    if v___x_457_ == 0 {
                        v___x_458_ = l_Lean_Expr_isApp(v___x_455_);
                        if v___x_458_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_455_);
                            crate::leanh::lean_dec_ref(v_arg_454_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_459_ = crate::leanh::lean_ctor_get(v___x_455_, 1);
                            crate::leanh::lean_inc_ref(v_arg_459_);
                            v___x_460_ = l_Lean_Expr_appFnCleanup___redArg(v___x_455_);
                            v___x_461_ = l_Lean_Expr_isApp(v___x_460_);
                            if v___x_461_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_460_);
                                crate::leanh::lean_dec_ref(v_arg_459_);
                                crate::leanh::lean_dec_ref(v_arg_454_);
                                state = 1;
                                continue;
                            } else {
                                v___x_462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_460_);
                                v___x_463_ = l_Lean_Meta_Sym_isOffset___closed__2;
                                v___x_464_ = l_Lean_Expr_isConstOf(v___x_462_, v___x_463_);
                                if v___x_464_ == 0 {
                                    v___x_465_ = l_Lean_Expr_isApp(v___x_462_);
                                    if v___x_465_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_462_);
                                        crate::leanh::lean_dec_ref(v_arg_459_);
                                        crate::leanh::lean_dec_ref(v_arg_454_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_466_ = l_Lean_Expr_appFnCleanup___redArg(v___x_462_);
                                        v___x_467_ = l_Lean_Expr_isApp(v___x_466_);
                                        if v___x_467_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_466_);
                                            crate::leanh::lean_dec_ref(v_arg_459_);
                                            crate::leanh::lean_dec_ref(v_arg_454_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_468_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_466_);
                                            v___x_469_ = l_Lean_Expr_isApp(v___x_468_);
                                            if v___x_469_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_468_);
                                                crate::leanh::lean_dec_ref(v_arg_459_);
                                                crate::leanh::lean_dec_ref(v_arg_454_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_470_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_468_);
                                                v___x_471_ =
                                                    l_Lean_Meta_Sym_isOffset_x3f___closed__5;
                                                v___x_472_ =
                                                    l_Lean_Expr_isConstOf(v___x_470_, v___x_471_);
                                                crate::leanh::lean_dec_ref(v___x_470_);
                                                if v___x_472_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_459_);
                                                    crate::leanh::lean_dec_ref(v_arg_454_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_473_ =
                                                        l_Lean_Meta_Sym_getNatValue_x3f(v_arg_454_);
                                                    if crate::leanh::lean_obj_tag(v___x_473_) == 1 {
                                                        crate::leanh::lean_dec_ref(v_e_445_);
                                                        v_val_474_ = crate::leanh::lean_ctor_get(
                                                            v___x_473_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_474_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_473_, 1,
                                                        );
                                                        v___x_475_ =
                                                            l_Lean_Meta_Sym_toOffset(v_arg_459_);
                                                        v___x_476_ = l_Lean_Meta_Sym_Offset_inc(
                                                            v___x_475_, v_val_474_,
                                                        );
                                                        crate::leanh::lean_dec(v_val_474_);
                                                        return v___x_476_;
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_473_);
                                                        crate::leanh::lean_dec_ref(v_arg_459_);
                                                        v___x_477_ =
                                                            crate::leanh::lean_unsigned_to_nat(0);
                                                        v___x_478_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_478_, 0, v_e_445_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_478_, 1, v___x_477_,
                                                        );
                                                        return v___x_478_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_462_);
                                    crate::leanh::lean_dec_ref(v_arg_454_);
                                    if crate::leanh::lean_obj_tag(v_arg_459_) == 9 {
                                        v_a_479_ = crate::leanh::lean_ctor_get(v_arg_459_, 0);
                                        crate::leanh::lean_inc_ref(v_a_479_);
                                        crate::leanh::lean_dec_ref_known(v_arg_459_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_479_) == 0 {
                                            crate::leanh::lean_dec_ref(v_e_445_);
                                            v_val_480_ = crate::leanh::lean_ctor_get(v_a_479_, 0);
                                            v_isSharedCheck_487_ =
                                                (!crate::leanh::lean_is_exclusive(v_a_479_)) as u8;
                                            if v_isSharedCheck_487_ == 0 {
                                                v___x_482_ = v_a_479_;
                                                v_isShared_483_ = v_isSharedCheck_487_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_val_480_);
                                                crate::leanh::lean_dec(v_a_479_);
                                                v___x_482_ = crate::leanh::lean_box(0);
                                                v_isShared_483_ = v_isSharedCheck_487_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_a_479_);
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_459_);
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_455_);
                        crate::leanh::lean_dec_ref(v_e_445_);
                        v___x_488_ = l_Lean_Meta_Sym_toOffset(v_arg_454_);
                        v___x_489_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_490_ = l_Lean_Meta_Sym_Offset_inc(v___x_488_, v___x_489_);
                        return v___x_490_;
                    }
                }
            }
            1 => {
                v___x_447_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_448_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_448_, 0, v_e_445_);
                crate::leanh::lean_ctor_set(v___x_448_, 1, v___x_447_);
                return v___x_448_;
            }
            2 => {
                v___x_450_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_451_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_451_, 0, v_e_445_);
                crate::leanh::lean_ctor_set(v___x_451_, 1, v___x_450_);
                return v___x_451_;
            }
            3 => {
                if v_isShared_483_ == 0 {
                    v___x_485_ = v___x_482_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_486_, 0, v_val_480_);
                    v___x_485_ = v_reuseFailAlloc_486_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_485_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Offset(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Offset(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Offset(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Offset(builtin);
}
