// Lean compiler output
// Module: Init.Control.EState
// Imports: Init.Data.ToString.Basic Init.Control.State
use crate::ffi::lean_string_append;
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
pub static l_EStateM_instToStringResult___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [111, 107, 58, 32, 0],
};
static mut l_EStateM_instToStringResult___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instToStringResult___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instToStringResult___redArg___lam__0___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 114, 114, 111, 114, 58, 32, 0],
};
static mut l_EStateM_instToStringResult___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instToStringResult___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        69, 83, 116, 97, 116, 101, 77, 46, 82, 101, 115, 117, 108, 116, 46, 111, 107, 32, 0,
    ],
};
static mut l_EStateM_instReprResult___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_EStateM_instReprResult___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__2_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        69, 83, 116, 97, 116, 101, 77, 46, 82, 101, 115, 117, 108, 116, 46, 101, 114, 114, 111,
        114, 32, 0,
    ],
};
static mut l_EStateM_instReprResult___redArg___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_EStateM_instReprResult___redArg___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instMonadAttach___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_instMonadAttach___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_EStateM_instMonadAttach___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadAttach___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_EStateM_instMonadFinally___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_EStateM_instMonadFinally___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_EStateM_instMonadFinally___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadFinally___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_EStateM_instToStringResult___redArg___lam__0(
    mut v_inst_255_: *mut leanh::LeanObject,
    mut v_inst_256_: *mut leanh::LeanObject,
    mut v_x_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v_a_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_256_);
        v_a_258_ = leanh::lean_ctor_get(v_x_257_, 0);
        leanh::lean_inc(v_a_258_);
        leanh::lean_dec_ref_known(v_x_257_, 2);
        v___x_259_ = l_EStateM_instToStringResult___redArg___lam__0___closed__0;
        v___x_260_ = leanh::lean_apply_1(v_inst_255_, v_a_258_);
        v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
        leanh::lean_dec_ref(v___x_260_);
        return v___x_261_;
    } else {
        let mut v_a_262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_255_);
        v_a_262_ = leanh::lean_ctor_get(v_x_257_, 0);
        leanh::lean_inc(v_a_262_);
        leanh::lean_dec_ref_known(v_x_257_, 2);
        v___x_263_ = l_EStateM_instToStringResult___redArg___lam__0___closed__1;
        v___x_264_ = leanh::lean_apply_1(v_inst_256_, v_a_262_);
        v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
        leanh::lean_dec_ref(v___x_264_);
        return v___x_265_;
    }
}
pub unsafe fn l_EStateM_instToStringResult___redArg(
    mut v_inst_266_: *mut leanh::LeanObject,
    mut v_inst_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_268_ = leanh::lean_alloc_closure(
        l_EStateM_instToStringResult___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_268_, 0, v_inst_267_);
    leanh::lean_closure_set(v___f_268_, 1, v_inst_266_);
    return v___f_268_;
}
pub unsafe fn l_EStateM_instToStringResult(
    mut v_00_u03b5_269_: *mut leanh::LeanObject,
    mut v_00_u03c3_270_: *mut leanh::LeanObject,
    mut v_00_u03b1_271_: *mut leanh::LeanObject,
    mut v_inst_272_: *mut leanh::LeanObject,
    mut v_inst_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_274_ = leanh::lean_alloc_closure(
        l_EStateM_instToStringResult___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_274_, 0, v_inst_273_);
    leanh::lean_closure_set(v___f_274_, 1, v_inst_272_);
    return v___f_274_;
}
pub unsafe fn l_EStateM_instReprResult___redArg___lam__0(
    mut v_inst_281_: *mut leanh::LeanObject,
    mut v_inst_282_: *mut leanh::LeanObject,
    mut v_x_283_: *mut leanh::LeanObject,
    mut v_x_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_296_: u8 = 0;
    let mut v_unused_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_301_: u8 = 0;
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_309_: u8 = 0;
    let mut v_unused_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_283_) == 0 {
                    leanh::lean_dec_ref(v_inst_282_);
                    v_a_285_ = leanh::lean_ctor_get(v_x_283_, 0);
                    v_isSharedCheck_296_ = (!leanh::lean_is_exclusive(v_x_283_)) as u8;
                    if v_isSharedCheck_296_ == 0 {
                        v_unused_297_ = leanh::lean_ctor_get(v_x_283_, 1);
                        leanh::lean_dec(v_unused_297_);
                        v___x_287_ = v_x_283_;
                        v_isShared_288_ = v_isSharedCheck_296_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_285_);
                        leanh::lean_dec(v_x_283_);
                        v___x_287_ = leanh::lean_box(0);
                        v_isShared_288_ = v_isSharedCheck_296_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_281_);
                    v_a_298_ = leanh::lean_ctor_get(v_x_283_, 0);
                    v_isSharedCheck_309_ = (!leanh::lean_is_exclusive(v_x_283_)) as u8;
                    if v_isSharedCheck_309_ == 0 {
                        v_unused_310_ = leanh::lean_ctor_get(v_x_283_, 1);
                        leanh::lean_dec(v_unused_310_);
                        v___x_300_ = v_x_283_;
                        v_isShared_301_ = v_isSharedCheck_309_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_298_);
                        leanh::lean_dec(v_x_283_);
                        v___x_300_ = leanh::lean_box(0);
                        v_isShared_301_ = v_isSharedCheck_309_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_289_ = l_EStateM_instReprResult___redArg___lam__0___closed__1;
                v___x_290_ = leanh::lean_unsigned_to_nat(1024);
                v___x_291_ = leanh::lean_apply_2(v_inst_281_, v_a_285_, v___x_290_);
                if v_isShared_288_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_287_, 5);
                    leanh::lean_ctor_set(v___x_287_, 1, v___x_291_);
                    leanh::lean_ctor_set(v___x_287_, 0, v___x_289_);
                    v___x_293_ = v___x_287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_295_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_291_);
                    v___x_293_ = v_reuseFailAlloc_295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_294_ = l_Repr_addAppParen(v___x_293_, v_x_284_);
                return v___x_294_;
            }
            3 => {
                v___x_302_ = l_EStateM_instReprResult___redArg___lam__0___closed__3;
                v___x_303_ = leanh::lean_unsigned_to_nat(1024);
                v___x_304_ = leanh::lean_apply_2(v_inst_282_, v_a_298_, v___x_303_);
                if v_isShared_301_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_300_, 5);
                    leanh::lean_ctor_set(v___x_300_, 1, v___x_304_);
                    leanh::lean_ctor_set(v___x_300_, 0, v___x_302_);
                    v___x_306_ = v___x_300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_308_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_304_);
                    v___x_306_ = v_reuseFailAlloc_308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_307_ = l_Repr_addAppParen(v___x_306_, v_x_284_);
                return v___x_307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instReprResult___redArg___lam__0___boxed(
    mut v_inst_311_: *mut leanh::LeanObject,
    mut v_inst_312_: *mut leanh::LeanObject,
    mut v_x_313_: *mut leanh::LeanObject,
    mut v_x_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ =
        l_EStateM_instReprResult___redArg___lam__0(v_inst_311_, v_inst_312_, v_x_313_, v_x_314_);
    leanh::lean_dec(v_x_314_);
    return v_res_315_;
}
pub unsafe fn l_EStateM_instReprResult___redArg(
    mut v_inst_316_: *mut leanh::LeanObject,
    mut v_inst_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_318_ = leanh::lean_alloc_closure(
        l_EStateM_instReprResult___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_318_, 0, v_inst_317_);
    leanh::lean_closure_set(v___f_318_, 1, v_inst_316_);
    return v___f_318_;
}
pub unsafe fn l_EStateM_instReprResult(
    mut v_00_u03b5_319_: *mut leanh::LeanObject,
    mut v_00_u03c3_320_: *mut leanh::LeanObject,
    mut v_00_u03b1_321_: *mut leanh::LeanObject,
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_inst_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_324_ = leanh::lean_alloc_closure(
        l_EStateM_instReprResult___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_324_, 0, v_inst_323_);
    leanh::lean_closure_set(v___f_324_, 1, v_inst_322_);
    return v___f_324_;
}
pub unsafe fn l_EStateM_instMonadAttach___lam__0(
    mut v_00_u03b1_325_: *mut leanh::LeanObject,
    mut v_x_326_: *mut leanh::LeanObject,
    mut v_s_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_333_: u8 = 0;
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_337_: u8 = 0;
    let mut v_a_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_328_ = leanh::lean_apply_1(v_x_326_, v_s_327_);
                if leanh::lean_obj_tag(v___x_328_) == 0 {
                    v_a_329_ = leanh::lean_ctor_get(v___x_328_, 0);
                    v_a_330_ = leanh::lean_ctor_get(v___x_328_, 1);
                    v_isSharedCheck_337_ = (!leanh::lean_is_exclusive(v___x_328_)) as u8;
                    if v_isSharedCheck_337_ == 0 {
                        v___x_332_ = v___x_328_;
                        v_isShared_333_ = v_isSharedCheck_337_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_330_);
                        leanh::lean_inc(v_a_329_);
                        leanh::lean_dec(v___x_328_);
                        v___x_332_ = leanh::lean_box(0);
                        v_isShared_333_ = v_isSharedCheck_337_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_338_ = leanh::lean_ctor_get(v___x_328_, 0);
                    v_a_339_ = leanh::lean_ctor_get(v___x_328_, 1);
                    v_isSharedCheck_346_ = (!leanh::lean_is_exclusive(v___x_328_)) as u8;
                    if v_isSharedCheck_346_ == 0 {
                        v___x_341_ = v___x_328_;
                        v_isShared_342_ = v_isSharedCheck_346_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_339_);
                        leanh::lean_inc(v_a_338_);
                        leanh::lean_dec(v___x_328_);
                        v___x_341_ = leanh::lean_box(0);
                        v_isShared_342_ = v_isSharedCheck_346_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_333_ == 0 {
                    v___x_335_ = v___x_332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_336_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_336_, 1, v_a_330_);
                    v___x_335_ = v_reuseFailAlloc_336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_335_;
            }
            3 => {
                if v_isShared_342_ == 0 {
                    v___x_344_ = v___x_341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_345_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_345_, 1, v_a_339_);
                    v___x_344_ = v_reuseFailAlloc_345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instMonadAttach(
    mut v_00_u03b5_348_: *mut leanh::LeanObject,
    mut v_00_u03c3_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_350_ = l_EStateM_instMonadAttach___closed__0;
    return v___f_350_;
}
pub unsafe fn l_EStateM_orElse_x27___redArg(
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_x_u2081_352_: *mut leanh::LeanObject,
    mut v_x_u2082_353_: *mut leanh::LeanObject,
    mut v_useFirstEx_354_: u8,
    mut v_s_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_save_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restore_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_371_: u8 = 0;
    let mut v_unused_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_save_356_ = leanh::lean_ctor_get(v_inst_351_, 0);
                leanh::lean_inc(v_save_356_);
                v_restore_357_ = leanh::lean_ctor_get(v_inst_351_, 1);
                leanh::lean_inc(v_restore_357_);
                leanh::lean_dec_ref(v_inst_351_);
                leanh::lean_inc(v_s_355_);
                v_d_358_ = leanh::lean_apply_1(v_save_356_, v_s_355_);
                v___x_359_ = leanh::lean_apply_1(v_x_u2081_352_, v_s_355_);
                if leanh::lean_obj_tag(v___x_359_) == 1 {
                    v_a_360_ = leanh::lean_ctor_get(v___x_359_, 0);
                    leanh::lean_inc(v_a_360_);
                    v_a_361_ = leanh::lean_ctor_get(v___x_359_, 1);
                    leanh::lean_inc(v_a_361_);
                    leanh::lean_dec_ref_known(v___x_359_, 2);
                    v___x_362_ = leanh::lean_apply_2(v_restore_357_, v_a_361_, v_d_358_);
                    v___x_363_ = leanh::lean_apply_1(v_x_u2082_353_, v___x_362_);
                    if leanh::lean_obj_tag(v___x_363_) == 1 {
                        if v_useFirstEx_354_ == 0 {
                            leanh::lean_dec(v_a_360_);
                            return v___x_363_;
                        } else {
                            v_a_364_ = leanh::lean_ctor_get(v___x_363_, 1);
                            v_isSharedCheck_371_ =
                                (!leanh::lean_is_exclusive(v___x_363_)) as u8;
                            if v_isSharedCheck_371_ == 0 {
                                v_unused_372_ = leanh::lean_ctor_get(v___x_363_, 0);
                                leanh::lean_dec(v_unused_372_);
                                v___x_366_ = v___x_363_;
                                v_isShared_367_ = v_isSharedCheck_371_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_364_);
                                leanh::lean_dec(v___x_363_);
                                v___x_366_ = leanh::lean_box(0);
                                v_isShared_367_ = v_isSharedCheck_371_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_360_);
                        return v___x_363_;
                    }
                } else {
                    leanh::lean_dec(v_d_358_);
                    leanh::lean_dec(v_restore_357_);
                    leanh::lean_dec_ref(v_x_u2082_353_);
                    return v___x_359_;
                }
            }
            1 => {
                if v_isShared_367_ == 0 {
                    leanh::lean_ctor_set(v___x_366_, 0, v_a_360_);
                    v___x_369_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_370_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_364_);
                    v___x_369_ = v_reuseFailAlloc_370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_orElse_x27___redArg___boxed(
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_x_u2081_374_: *mut leanh::LeanObject,
    mut v_x_u2082_375_: *mut leanh::LeanObject,
    mut v_useFirstEx_376_: *mut leanh::LeanObject,
    mut v_s_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useFirstEx_boxed_378_: u8 = 0;
    let mut v_res_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_378_ = (leanh::lean_unbox(v_useFirstEx_376_) as u8);
    v_res_379_ = l_EStateM_orElse_x27___redArg(
        v_inst_373_,
        v_x_u2081_374_,
        v_x_u2082_375_,
        v_useFirstEx_boxed_378_,
        v_s_377_,
    );
    return v_res_379_;
}
pub unsafe fn l_EStateM_orElse_x27(
    mut v_00_u03b5_380_: *mut leanh::LeanObject,
    mut v_00_u03c3_381_: *mut leanh::LeanObject,
    mut v_00_u03b1_382_: *mut leanh::LeanObject,
    mut v_00_u03b4_383_: *mut leanh::LeanObject,
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_x_u2081_385_: *mut leanh::LeanObject,
    mut v_x_u2082_386_: *mut leanh::LeanObject,
    mut v_useFirstEx_387_: u8,
    mut v_s_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_save_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restore_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_400_: u8 = 0;
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_404_: u8 = 0;
    let mut v_unused_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_save_389_ = leanh::lean_ctor_get(v_inst_384_, 0);
                leanh::lean_inc(v_save_389_);
                v_restore_390_ = leanh::lean_ctor_get(v_inst_384_, 1);
                leanh::lean_inc(v_restore_390_);
                leanh::lean_dec_ref(v_inst_384_);
                leanh::lean_inc(v_s_388_);
                v_d_391_ = leanh::lean_apply_1(v_save_389_, v_s_388_);
                v___x_392_ = leanh::lean_apply_1(v_x_u2081_385_, v_s_388_);
                if leanh::lean_obj_tag(v___x_392_) == 1 {
                    v_a_393_ = leanh::lean_ctor_get(v___x_392_, 0);
                    leanh::lean_inc(v_a_393_);
                    v_a_394_ = leanh::lean_ctor_get(v___x_392_, 1);
                    leanh::lean_inc(v_a_394_);
                    leanh::lean_dec_ref_known(v___x_392_, 2);
                    v___x_395_ = leanh::lean_apply_2(v_restore_390_, v_a_394_, v_d_391_);
                    v___x_396_ = leanh::lean_apply_1(v_x_u2082_386_, v___x_395_);
                    if leanh::lean_obj_tag(v___x_396_) == 1 {
                        if v_useFirstEx_387_ == 0 {
                            leanh::lean_dec(v_a_393_);
                            return v___x_396_;
                        } else {
                            v_a_397_ = leanh::lean_ctor_get(v___x_396_, 1);
                            v_isSharedCheck_404_ =
                                (!leanh::lean_is_exclusive(v___x_396_)) as u8;
                            if v_isSharedCheck_404_ == 0 {
                                v_unused_405_ = leanh::lean_ctor_get(v___x_396_, 0);
                                leanh::lean_dec(v_unused_405_);
                                v___x_399_ = v___x_396_;
                                v_isShared_400_ = v_isSharedCheck_404_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_397_);
                                leanh::lean_dec(v___x_396_);
                                v___x_399_ = leanh::lean_box(0);
                                v_isShared_400_ = v_isSharedCheck_404_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_393_);
                        return v___x_396_;
                    }
                } else {
                    leanh::lean_dec(v_d_391_);
                    leanh::lean_dec(v_restore_390_);
                    leanh::lean_dec_ref(v_x_u2082_386_);
                    return v___x_392_;
                }
            }
            1 => {
                if v_isShared_400_ == 0 {
                    leanh::lean_ctor_set(v___x_399_, 0, v_a_393_);
                    v___x_402_ = v___x_399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_403_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_397_);
                    v___x_402_ = v_reuseFailAlloc_403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_orElse_x27___boxed(
    mut v_00_u03b5_406_: *mut leanh::LeanObject,
    mut v_00_u03c3_407_: *mut leanh::LeanObject,
    mut v_00_u03b1_408_: *mut leanh::LeanObject,
    mut v_00_u03b4_409_: *mut leanh::LeanObject,
    mut v_inst_410_: *mut leanh::LeanObject,
    mut v_x_u2081_411_: *mut leanh::LeanObject,
    mut v_x_u2082_412_: *mut leanh::LeanObject,
    mut v_useFirstEx_413_: *mut leanh::LeanObject,
    mut v_s_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useFirstEx_boxed_415_: u8 = 0;
    let mut v_res_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_415_ = (leanh::lean_unbox(v_useFirstEx_413_) as u8);
    v_res_416_ = l_EStateM_orElse_x27(
        v_00_u03b5_406_,
        v_00_u03c3_407_,
        v_00_u03b1_408_,
        v_00_u03b4_409_,
        v_inst_410_,
        v_x_u2081_411_,
        v_x_u2082_412_,
        v_useFirstEx_boxed_415_,
        v_s_414_,
    );
    return v_res_416_;
}
pub unsafe fn l_EStateM_instMonadFinally___lam__0(
    mut v_00_u03b1_417_: *mut leanh::LeanObject,
    mut v_00_u03b2_418_: *mut leanh::LeanObject,
    mut v_x_419_: *mut leanh::LeanObject,
    mut v_h_420_: *mut leanh::LeanObject,
    mut v_s_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_441_: u8 = 0;
    let mut v_a_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut v_isSharedCheck_451_: u8 = 0;
    let mut v_a_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut v_unused_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_469_: u8 = 0;
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_422_ = leanh::lean_apply_1(v_x_419_, v_s_421_);
                if leanh::lean_obj_tag(v_r_422_) == 0 {
                    v_a_423_ = leanh::lean_ctor_get(v_r_422_, 0);
                    v_a_424_ = leanh::lean_ctor_get(v_r_422_, 1);
                    v_isSharedCheck_451_ = (!leanh::lean_is_exclusive(v_r_422_)) as u8;
                    if v_isSharedCheck_451_ == 0 {
                        v___x_426_ = v_r_422_;
                        v_isShared_427_ = v_isSharedCheck_451_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_424_);
                        leanh::lean_inc(v_a_423_);
                        leanh::lean_dec(v_r_422_);
                        v___x_426_ = leanh::lean_box(0);
                        v_isShared_427_ = v_isSharedCheck_451_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_452_ = leanh::lean_ctor_get(v_r_422_, 0);
                    leanh::lean_inc(v_a_452_);
                    v_a_453_ = leanh::lean_ctor_get(v_r_422_, 1);
                    leanh::lean_inc(v_a_453_);
                    leanh::lean_dec_ref_known(v_r_422_, 2);
                    v___x_454_ = leanh::lean_box(0);
                    v___x_455_ = leanh::lean_apply_2(v_h_420_, v___x_454_, v_a_453_);
                    if leanh::lean_obj_tag(v___x_455_) == 0 {
                        v_a_456_ = leanh::lean_ctor_get(v___x_455_, 1);
                        v_isSharedCheck_463_ = (!leanh::lean_is_exclusive(v___x_455_)) as u8;
                        if v_isSharedCheck_463_ == 0 {
                            v_unused_464_ = leanh::lean_ctor_get(v___x_455_, 0);
                            leanh::lean_dec(v_unused_464_);
                            v___x_458_ = v___x_455_;
                            v_isShared_459_ = v_isSharedCheck_463_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_456_);
                            leanh::lean_dec(v___x_455_);
                            v___x_458_ = leanh::lean_box(0);
                            v_isShared_459_ = v_isSharedCheck_463_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_452_);
                        v_a_465_ = leanh::lean_ctor_get(v___x_455_, 0);
                        v_a_466_ = leanh::lean_ctor_get(v___x_455_, 1);
                        v_isSharedCheck_473_ = (!leanh::lean_is_exclusive(v___x_455_)) as u8;
                        if v_isSharedCheck_473_ == 0 {
                            v___x_468_ = v___x_455_;
                            v_isShared_469_ = v_isSharedCheck_473_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_466_);
                            leanh::lean_inc(v_a_465_);
                            leanh::lean_dec(v___x_455_);
                            v___x_468_ = leanh::lean_box(0);
                            v_isShared_469_ = v_isSharedCheck_473_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_423_);
                v___x_428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_428_, 0, v_a_423_);
                v___x_429_ = leanh::lean_apply_2(v_h_420_, v___x_428_, v_a_424_);
                if leanh::lean_obj_tag(v___x_429_) == 0 {
                    v_a_430_ = leanh::lean_ctor_get(v___x_429_, 0);
                    v_a_431_ = leanh::lean_ctor_get(v___x_429_, 1);
                    v_isSharedCheck_441_ = (!leanh::lean_is_exclusive(v___x_429_)) as u8;
                    if v_isSharedCheck_441_ == 0 {
                        v___x_433_ = v___x_429_;
                        v_isShared_434_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_431_);
                        leanh::lean_inc(v_a_430_);
                        leanh::lean_dec(v___x_429_);
                        v___x_433_ = leanh::lean_box(0);
                        v_isShared_434_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_426_);
                    leanh::lean_dec(v_a_423_);
                    v_a_442_ = leanh::lean_ctor_get(v___x_429_, 0);
                    v_a_443_ = leanh::lean_ctor_get(v___x_429_, 1);
                    v_isSharedCheck_450_ = (!leanh::lean_is_exclusive(v___x_429_)) as u8;
                    if v_isSharedCheck_450_ == 0 {
                        v___x_445_ = v___x_429_;
                        v_isShared_446_ = v_isSharedCheck_450_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_443_);
                        leanh::lean_inc(v_a_442_);
                        leanh::lean_dec(v___x_429_);
                        v___x_445_ = leanh::lean_box(0);
                        v_isShared_446_ = v_isSharedCheck_450_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_427_ == 0 {
                    leanh::lean_ctor_set(v___x_426_, 1, v_a_430_);
                    v___x_436_ = v___x_426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_440_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_440_, 1, v_a_430_);
                    v___x_436_ = v_reuseFailAlloc_440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_434_ == 0 {
                    leanh::lean_ctor_set(v___x_433_, 0, v___x_436_);
                    v___x_438_ = v___x_433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_439_, 1, v_a_431_);
                    v___x_438_ = v_reuseFailAlloc_439_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_438_;
            }
            5 => {
                if v_isShared_446_ == 0 {
                    v___x_448_ = v___x_445_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_449_, 1, v_a_443_);
                    v___x_448_ = v_reuseFailAlloc_449_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_448_;
            }
            7 => {
                if v_isShared_459_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_458_, 1);
                    leanh::lean_ctor_set(v___x_458_, 0, v_a_452_);
                    v___x_461_ = v___x_458_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_462_, 1, v_a_456_);
                    v___x_461_ = v_reuseFailAlloc_462_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_461_;
            }
            9 => {
                if v_isShared_469_ == 0 {
                    v___x_471_ = v___x_468_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_472_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_472_, 1, v_a_466_);
                    v___x_471_ = v_reuseFailAlloc_472_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_instMonadFinally(
    mut v_00_u03b5_475_: *mut leanh::LeanObject,
    mut v_00_u03c3_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_477_ = l_EStateM_instMonadFinally___closed__0;
    return v___f_477_;
}
pub unsafe fn l_EStateM_fromStateM___redArg(
    mut v_x_478_: *mut leanh::LeanObject,
    mut v_s_479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_485_: u8 = 0;
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_480_ = leanh::lean_apply_1(v_x_478_, v_s_479_);
                v_fst_481_ = leanh::lean_ctor_get(v___x_480_, 0);
                v_snd_482_ = leanh::lean_ctor_get(v___x_480_, 1);
                v_isSharedCheck_489_ = (!leanh::lean_is_exclusive(v___x_480_)) as u8;
                if v_isSharedCheck_489_ == 0 {
                    v___x_484_ = v___x_480_;
                    v_isShared_485_ = v_isSharedCheck_489_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_482_);
                    leanh::lean_inc(v_fst_481_);
                    leanh::lean_dec(v___x_480_);
                    v___x_484_ = leanh::lean_box(0);
                    v_isShared_485_ = v_isSharedCheck_489_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_485_ == 0 {
                    v___x_487_ = v___x_484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_488_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fst_481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_482_);
                    v___x_487_ = v_reuseFailAlloc_488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_EStateM_fromStateM(
    mut v_00_u03b5_490_: *mut leanh::LeanObject,
    mut v_00_u03c3_491_: *mut leanh::LeanObject,
    mut v_00_u03b1_492_: *mut leanh::LeanObject,
    mut v_x_493_: *mut leanh::LeanObject,
    mut v_s_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_495_ = leanh::lean_apply_1(v_x_493_, v_s_494_);
                v_fst_496_ = leanh::lean_ctor_get(v___x_495_, 0);
                v_snd_497_ = leanh::lean_ctor_get(v___x_495_, 1);
                v_isSharedCheck_504_ = (!leanh::lean_is_exclusive(v___x_495_)) as u8;
                if v_isSharedCheck_504_ == 0 {
                    v___x_499_ = v___x_495_;
                    v_isShared_500_ = v_isSharedCheck_504_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_497_);
                    leanh::lean_inc(v_fst_496_);
                    leanh::lean_dec(v___x_495_);
                    v___x_499_ = leanh::lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_504_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_500_ == 0 {
                    v___x_502_ = v___x_499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_503_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_503_, 0, v_fst_496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_503_, 1, v_snd_497_);
                    v___x_502_ = v_reuseFailAlloc_503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_502_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_EState(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_EState(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_EState(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_EState(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_EState(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_EState(builtin);
}