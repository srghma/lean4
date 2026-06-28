// Lean compiler output
// Module: Init.Control.EState
// Imports: Init.Data.ToString.Basic Init.Control.State
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_append;
pub static l_EStateM_instToStringResult___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instToStringResult___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instToStringResult___redArg___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instToStringResult___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_EStateM_instReprResult___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_EStateM_instReprResult___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_EStateM_instReprResult___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instReprResult___redArg___lam__0___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_EStateM_instReprResult___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instReprResult___redArg___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instMonadAttach___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_EStateM_instMonadAttach___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_EStateM_instMonadAttach___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadAttach___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_EStateM_instMonadFinally___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_EStateM_instMonadFinally___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_EStateM_instMonadFinally___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_EStateM_instMonadFinally___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_EStateM_instToStringResult___redArg___lam__0(
    mut v_inst_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
    mut v_x_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_257_) == 0 {
        let mut v_a_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_256_);
        v_a_258_ = crate::leanh::lean_ctor_get(v_x_257_, 0);
        crate::leanh::lean_inc(v_a_258_);
        crate::leanh::lean_dec_ref_known(v_x_257_, 2);
        v___x_259_ = l_EStateM_instToStringResult___redArg___lam__0___closed__0;
        v___x_260_ = crate::leanh::lean_apply_1(v_inst_255_, v_a_258_);
        v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
        crate::leanh::lean_dec_ref(v___x_260_);
        return v___x_261_;
    } else {
        let mut v_a_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_255_);
        v_a_262_ = crate::leanh::lean_ctor_get(v_x_257_, 0);
        crate::leanh::lean_inc(v_a_262_);
        crate::leanh::lean_dec_ref_known(v_x_257_, 2);
        v___x_263_ = l_EStateM_instToStringResult___redArg___lam__0___closed__1;
        v___x_264_ = crate::leanh::lean_apply_1(v_inst_256_, v_a_262_);
        v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
        crate::leanh::lean_dec_ref(v___x_264_);
        return v___x_265_;
    }
}
pub unsafe fn l_EStateM_instToStringResult___redArg(
    mut v_inst_266_: *mut crate::leanh::LeanObject,
    mut v_inst_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_268_ = crate::leanh::lean_alloc_closure(
        l_EStateM_instToStringResult___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_268_, 0, v_inst_267_);
    crate::leanh::lean_closure_set(v___f_268_, 1, v_inst_266_);
    return v___f_268_;
}
pub unsafe fn l_EStateM_instToStringResult(
    mut v_00_u03b5_269_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_270_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_271_: *mut crate::leanh::LeanObject,
    mut v_inst_272_: *mut crate::leanh::LeanObject,
    mut v_inst_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_274_ = crate::leanh::lean_alloc_closure(
        l_EStateM_instToStringResult___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_274_, 0, v_inst_273_);
    crate::leanh::lean_closure_set(v___f_274_, 1, v_inst_272_);
    return v___f_274_;
}
pub unsafe fn l_EStateM_instReprResult___redArg___lam__0(
    mut v_inst_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
    mut v_x_283_: *mut crate::leanh::LeanObject,
    mut v_x_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_296_: u8 = 0;
    let mut v_unused_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_301_: u8 = 0;
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_309_: u8 = 0;
    let mut v_unused_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_283_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_282_);
                    v_a_285_ = crate::leanh::lean_ctor_get(v_x_283_, 0);
                    v_isSharedCheck_296_ = (!crate::leanh::lean_is_exclusive(v_x_283_)) as u8;
                    if v_isSharedCheck_296_ == 0 {
                        v_unused_297_ = crate::leanh::lean_ctor_get(v_x_283_, 1);
                        crate::leanh::lean_dec(v_unused_297_);
                        v___x_287_ = v_x_283_;
                        v_isShared_288_ = v_isSharedCheck_296_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_285_);
                        crate::leanh::lean_dec(v_x_283_);
                        v___x_287_ = crate::leanh::lean_box(0);
                        v_isShared_288_ = v_isSharedCheck_296_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_281_);
                    v_a_298_ = crate::leanh::lean_ctor_get(v_x_283_, 0);
                    v_isSharedCheck_309_ = (!crate::leanh::lean_is_exclusive(v_x_283_)) as u8;
                    if v_isSharedCheck_309_ == 0 {
                        v_unused_310_ = crate::leanh::lean_ctor_get(v_x_283_, 1);
                        crate::leanh::lean_dec(v_unused_310_);
                        v___x_300_ = v_x_283_;
                        v_isShared_301_ = v_isSharedCheck_309_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_298_);
                        crate::leanh::lean_dec(v_x_283_);
                        v___x_300_ = crate::leanh::lean_box(0);
                        v_isShared_301_ = v_isSharedCheck_309_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_289_ = l_EStateM_instReprResult___redArg___lam__0___closed__1;
                v___x_290_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_291_ = crate::leanh::lean_apply_2(v_inst_281_, v_a_285_, v___x_290_);
                if v_isShared_288_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_287_, 5);
                    crate::leanh::lean_ctor_set(v___x_287_, 1, v___x_291_);
                    crate::leanh::lean_ctor_set(v___x_287_, 0, v___x_289_);
                    v___x_293_ = v___x_287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_295_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_291_);
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
                v___x_303_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_304_ = crate::leanh::lean_apply_2(v_inst_282_, v_a_298_, v___x_303_);
                if v_isShared_301_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_300_, 5);
                    crate::leanh::lean_ctor_set(v___x_300_, 1, v___x_304_);
                    crate::leanh::lean_ctor_set(v___x_300_, 0, v___x_302_);
                    v___x_306_ = v___x_300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_308_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_304_);
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
    mut v_inst_311_: *mut crate::leanh::LeanObject,
    mut v_inst_312_: *mut crate::leanh::LeanObject,
    mut v_x_313_: *mut crate::leanh::LeanObject,
    mut v_x_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ =
        l_EStateM_instReprResult___redArg___lam__0(v_inst_311_, v_inst_312_, v_x_313_, v_x_314_);
    crate::leanh::lean_dec(v_x_314_);
    return v_res_315_;
}
pub unsafe fn l_EStateM_instReprResult___redArg(
    mut v_inst_316_: *mut crate::leanh::LeanObject,
    mut v_inst_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_318_ = crate::leanh::lean_alloc_closure(
        l_EStateM_instReprResult___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_318_, 0, v_inst_317_);
    crate::leanh::lean_closure_set(v___f_318_, 1, v_inst_316_);
    return v___f_318_;
}
pub unsafe fn l_EStateM_instReprResult(
    mut v_00_u03b5_319_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_321_: *mut crate::leanh::LeanObject,
    mut v_inst_322_: *mut crate::leanh::LeanObject,
    mut v_inst_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_324_ = crate::leanh::lean_alloc_closure(
        l_EStateM_instReprResult___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_324_, 0, v_inst_323_);
    crate::leanh::lean_closure_set(v___f_324_, 1, v_inst_322_);
    return v___f_324_;
}
pub unsafe fn l_EStateM_instMonadAttach___lam__0(
    mut v_00_u03b1_325_: *mut crate::leanh::LeanObject,
    mut v_x_326_: *mut crate::leanh::LeanObject,
    mut v_s_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_333_: u8 = 0;
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_337_: u8 = 0;
    let mut v_a_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_328_ = crate::leanh::lean_apply_1(v_x_326_, v_s_327_);
                if crate::leanh::lean_obj_tag(v___x_328_) == 0 {
                    v_a_329_ = crate::leanh::lean_ctor_get(v___x_328_, 0);
                    v_a_330_ = crate::leanh::lean_ctor_get(v___x_328_, 1);
                    v_isSharedCheck_337_ = (!crate::leanh::lean_is_exclusive(v___x_328_)) as u8;
                    if v_isSharedCheck_337_ == 0 {
                        v___x_332_ = v___x_328_;
                        v_isShared_333_ = v_isSharedCheck_337_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_330_);
                        crate::leanh::lean_inc(v_a_329_);
                        crate::leanh::lean_dec(v___x_328_);
                        v___x_332_ = crate::leanh::lean_box(0);
                        v_isShared_333_ = v_isSharedCheck_337_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_338_ = crate::leanh::lean_ctor_get(v___x_328_, 0);
                    v_a_339_ = crate::leanh::lean_ctor_get(v___x_328_, 1);
                    v_isSharedCheck_346_ = (!crate::leanh::lean_is_exclusive(v___x_328_)) as u8;
                    if v_isSharedCheck_346_ == 0 {
                        v___x_341_ = v___x_328_;
                        v_isShared_342_ = v_isSharedCheck_346_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_339_);
                        crate::leanh::lean_inc(v_a_338_);
                        crate::leanh::lean_dec(v___x_328_);
                        v___x_341_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_336_, 1, v_a_330_);
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
                    v_reuseFailAlloc_345_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_345_, 1, v_a_339_);
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
    mut v_00_u03b5_348_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_350_ = l_EStateM_instMonadAttach___closed__0;
    return v___f_350_;
}
pub unsafe fn l_EStateM_orElse_x27___redArg(
    mut v_inst_351_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_352_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_353_: *mut crate::leanh::LeanObject,
    mut v_useFirstEx_354_: u8,
    mut v_s_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_save_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restore_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_371_: u8 = 0;
    let mut v_unused_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_save_356_ = crate::leanh::lean_ctor_get(v_inst_351_, 0);
                crate::leanh::lean_inc(v_save_356_);
                v_restore_357_ = crate::leanh::lean_ctor_get(v_inst_351_, 1);
                crate::leanh::lean_inc(v_restore_357_);
                crate::leanh::lean_dec_ref(v_inst_351_);
                crate::leanh::lean_inc(v_s_355_);
                v_d_358_ = crate::leanh::lean_apply_1(v_save_356_, v_s_355_);
                v___x_359_ = crate::leanh::lean_apply_1(v_x_u2081_352_, v_s_355_);
                if crate::leanh::lean_obj_tag(v___x_359_) == 1 {
                    v_a_360_ = crate::leanh::lean_ctor_get(v___x_359_, 0);
                    crate::leanh::lean_inc(v_a_360_);
                    v_a_361_ = crate::leanh::lean_ctor_get(v___x_359_, 1);
                    crate::leanh::lean_inc(v_a_361_);
                    crate::leanh::lean_dec_ref_known(v___x_359_, 2);
                    v___x_362_ = crate::leanh::lean_apply_2(v_restore_357_, v_a_361_, v_d_358_);
                    v___x_363_ = crate::leanh::lean_apply_1(v_x_u2082_353_, v___x_362_);
                    if crate::leanh::lean_obj_tag(v___x_363_) == 1 {
                        if v_useFirstEx_354_ == 0 {
                            crate::leanh::lean_dec(v_a_360_);
                            return v___x_363_;
                        } else {
                            v_a_364_ = crate::leanh::lean_ctor_get(v___x_363_, 1);
                            v_isSharedCheck_371_ =
                                (!crate::leanh::lean_is_exclusive(v___x_363_)) as u8;
                            if v_isSharedCheck_371_ == 0 {
                                v_unused_372_ = crate::leanh::lean_ctor_get(v___x_363_, 0);
                                crate::leanh::lean_dec(v_unused_372_);
                                v___x_366_ = v___x_363_;
                                v_isShared_367_ = v_isSharedCheck_371_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_364_);
                                crate::leanh::lean_dec(v___x_363_);
                                v___x_366_ = crate::leanh::lean_box(0);
                                v_isShared_367_ = v_isSharedCheck_371_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_360_);
                        return v___x_363_;
                    }
                } else {
                    crate::leanh::lean_dec(v_d_358_);
                    crate::leanh::lean_dec(v_restore_357_);
                    crate::leanh::lean_dec_ref(v_x_u2082_353_);
                    return v___x_359_;
                }
            }
            1 => {
                if v_isShared_367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_366_, 0, v_a_360_);
                    v___x_369_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_370_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_364_);
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
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_374_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_375_: *mut crate::leanh::LeanObject,
    mut v_useFirstEx_376_: *mut crate::leanh::LeanObject,
    mut v_s_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useFirstEx_boxed_378_: u8 = 0;
    let mut v_res_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_378_ = (crate::leanh::lean_unbox(v_useFirstEx_376_) as u8);
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
    mut v_00_u03b5_380_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_382_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_383_: *mut crate::leanh::LeanObject,
    mut v_inst_384_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_385_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_386_: *mut crate::leanh::LeanObject,
    mut v_useFirstEx_387_: u8,
    mut v_s_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_save_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restore_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_400_: u8 = 0;
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_404_: u8 = 0;
    let mut v_unused_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_save_389_ = crate::leanh::lean_ctor_get(v_inst_384_, 0);
                crate::leanh::lean_inc(v_save_389_);
                v_restore_390_ = crate::leanh::lean_ctor_get(v_inst_384_, 1);
                crate::leanh::lean_inc(v_restore_390_);
                crate::leanh::lean_dec_ref(v_inst_384_);
                crate::leanh::lean_inc(v_s_388_);
                v_d_391_ = crate::leanh::lean_apply_1(v_save_389_, v_s_388_);
                v___x_392_ = crate::leanh::lean_apply_1(v_x_u2081_385_, v_s_388_);
                if crate::leanh::lean_obj_tag(v___x_392_) == 1 {
                    v_a_393_ = crate::leanh::lean_ctor_get(v___x_392_, 0);
                    crate::leanh::lean_inc(v_a_393_);
                    v_a_394_ = crate::leanh::lean_ctor_get(v___x_392_, 1);
                    crate::leanh::lean_inc(v_a_394_);
                    crate::leanh::lean_dec_ref_known(v___x_392_, 2);
                    v___x_395_ = crate::leanh::lean_apply_2(v_restore_390_, v_a_394_, v_d_391_);
                    v___x_396_ = crate::leanh::lean_apply_1(v_x_u2082_386_, v___x_395_);
                    if crate::leanh::lean_obj_tag(v___x_396_) == 1 {
                        if v_useFirstEx_387_ == 0 {
                            crate::leanh::lean_dec(v_a_393_);
                            return v___x_396_;
                        } else {
                            v_a_397_ = crate::leanh::lean_ctor_get(v___x_396_, 1);
                            v_isSharedCheck_404_ =
                                (!crate::leanh::lean_is_exclusive(v___x_396_)) as u8;
                            if v_isSharedCheck_404_ == 0 {
                                v_unused_405_ = crate::leanh::lean_ctor_get(v___x_396_, 0);
                                crate::leanh::lean_dec(v_unused_405_);
                                v___x_399_ = v___x_396_;
                                v_isShared_400_ = v_isSharedCheck_404_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_397_);
                                crate::leanh::lean_dec(v___x_396_);
                                v___x_399_ = crate::leanh::lean_box(0);
                                v_isShared_400_ = v_isSharedCheck_404_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_393_);
                        return v___x_396_;
                    }
                } else {
                    crate::leanh::lean_dec(v_d_391_);
                    crate::leanh::lean_dec(v_restore_390_);
                    crate::leanh::lean_dec_ref(v_x_u2082_386_);
                    return v___x_392_;
                }
            }
            1 => {
                if v_isShared_400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_399_, 0, v_a_393_);
                    v___x_402_ = v___x_399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_403_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_397_);
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
    mut v_00_u03b5_406_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_407_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_409_: *mut crate::leanh::LeanObject,
    mut v_inst_410_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_411_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_412_: *mut crate::leanh::LeanObject,
    mut v_useFirstEx_413_: *mut crate::leanh::LeanObject,
    mut v_s_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useFirstEx_boxed_415_: u8 = 0;
    let mut v_res_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useFirstEx_boxed_415_ = (crate::leanh::lean_unbox(v_useFirstEx_413_) as u8);
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
    mut v_00_u03b1_417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_418_: *mut crate::leanh::LeanObject,
    mut v_x_419_: *mut crate::leanh::LeanObject,
    mut v_h_420_: *mut crate::leanh::LeanObject,
    mut v_s_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_441_: u8 = 0;
    let mut v_a_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut v_isSharedCheck_451_: u8 = 0;
    let mut v_a_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut v_unused_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_469_: u8 = 0;
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_422_ = crate::leanh::lean_apply_1(v_x_419_, v_s_421_);
                if crate::leanh::lean_obj_tag(v_r_422_) == 0 {
                    v_a_423_ = crate::leanh::lean_ctor_get(v_r_422_, 0);
                    v_a_424_ = crate::leanh::lean_ctor_get(v_r_422_, 1);
                    v_isSharedCheck_451_ = (!crate::leanh::lean_is_exclusive(v_r_422_)) as u8;
                    if v_isSharedCheck_451_ == 0 {
                        v___x_426_ = v_r_422_;
                        v_isShared_427_ = v_isSharedCheck_451_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_424_);
                        crate::leanh::lean_inc(v_a_423_);
                        crate::leanh::lean_dec(v_r_422_);
                        v___x_426_ = crate::leanh::lean_box(0);
                        v_isShared_427_ = v_isSharedCheck_451_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_452_ = crate::leanh::lean_ctor_get(v_r_422_, 0);
                    crate::leanh::lean_inc(v_a_452_);
                    v_a_453_ = crate::leanh::lean_ctor_get(v_r_422_, 1);
                    crate::leanh::lean_inc(v_a_453_);
                    crate::leanh::lean_dec_ref_known(v_r_422_, 2);
                    v___x_454_ = crate::leanh::lean_box(0);
                    v___x_455_ = crate::leanh::lean_apply_2(v_h_420_, v___x_454_, v_a_453_);
                    if crate::leanh::lean_obj_tag(v___x_455_) == 0 {
                        v_a_456_ = crate::leanh::lean_ctor_get(v___x_455_, 1);
                        v_isSharedCheck_463_ = (!crate::leanh::lean_is_exclusive(v___x_455_)) as u8;
                        if v_isSharedCheck_463_ == 0 {
                            v_unused_464_ = crate::leanh::lean_ctor_get(v___x_455_, 0);
                            crate::leanh::lean_dec(v_unused_464_);
                            v___x_458_ = v___x_455_;
                            v_isShared_459_ = v_isSharedCheck_463_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_456_);
                            crate::leanh::lean_dec(v___x_455_);
                            v___x_458_ = crate::leanh::lean_box(0);
                            v_isShared_459_ = v_isSharedCheck_463_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_452_);
                        v_a_465_ = crate::leanh::lean_ctor_get(v___x_455_, 0);
                        v_a_466_ = crate::leanh::lean_ctor_get(v___x_455_, 1);
                        v_isSharedCheck_473_ = (!crate::leanh::lean_is_exclusive(v___x_455_)) as u8;
                        if v_isSharedCheck_473_ == 0 {
                            v___x_468_ = v___x_455_;
                            v_isShared_469_ = v_isSharedCheck_473_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_466_);
                            crate::leanh::lean_inc(v_a_465_);
                            crate::leanh::lean_dec(v___x_455_);
                            v___x_468_ = crate::leanh::lean_box(0);
                            v_isShared_469_ = v_isSharedCheck_473_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_423_);
                v___x_428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_428_, 0, v_a_423_);
                v___x_429_ = crate::leanh::lean_apply_2(v_h_420_, v___x_428_, v_a_424_);
                if crate::leanh::lean_obj_tag(v___x_429_) == 0 {
                    v_a_430_ = crate::leanh::lean_ctor_get(v___x_429_, 0);
                    v_a_431_ = crate::leanh::lean_ctor_get(v___x_429_, 1);
                    v_isSharedCheck_441_ = (!crate::leanh::lean_is_exclusive(v___x_429_)) as u8;
                    if v_isSharedCheck_441_ == 0 {
                        v___x_433_ = v___x_429_;
                        v_isShared_434_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_431_);
                        crate::leanh::lean_inc(v_a_430_);
                        crate::leanh::lean_dec(v___x_429_);
                        v___x_433_ = crate::leanh::lean_box(0);
                        v_isShared_434_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_426_);
                    crate::leanh::lean_dec(v_a_423_);
                    v_a_442_ = crate::leanh::lean_ctor_get(v___x_429_, 0);
                    v_a_443_ = crate::leanh::lean_ctor_get(v___x_429_, 1);
                    v_isSharedCheck_450_ = (!crate::leanh::lean_is_exclusive(v___x_429_)) as u8;
                    if v_isSharedCheck_450_ == 0 {
                        v___x_445_ = v___x_429_;
                        v_isShared_446_ = v_isSharedCheck_450_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_443_);
                        crate::leanh::lean_inc(v_a_442_);
                        crate::leanh::lean_dec(v___x_429_);
                        v___x_445_ = crate::leanh::lean_box(0);
                        v_isShared_446_ = v_isSharedCheck_450_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_426_, 1, v_a_430_);
                    v___x_436_ = v___x_426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_440_, 1, v_a_430_);
                    v___x_436_ = v_reuseFailAlloc_440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_433_, 0, v___x_436_);
                    v___x_438_ = v___x_433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_439_, 1, v_a_431_);
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
                    v_reuseFailAlloc_449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_449_, 1, v_a_443_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_458_, 1);
                    crate::leanh::lean_ctor_set(v___x_458_, 0, v_a_452_);
                    v___x_461_ = v___x_458_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_462_, 1, v_a_456_);
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
                    v_reuseFailAlloc_472_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_472_, 1, v_a_466_);
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
    mut v_00_u03b5_475_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_477_ = l_EStateM_instMonadFinally___closed__0;
    return v___f_477_;
}
pub unsafe fn l_EStateM_fromStateM___redArg(
    mut v_x_478_: *mut crate::leanh::LeanObject,
    mut v_s_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_485_: u8 = 0;
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_480_ = crate::leanh::lean_apply_1(v_x_478_, v_s_479_);
                v_fst_481_ = crate::leanh::lean_ctor_get(v___x_480_, 0);
                v_snd_482_ = crate::leanh::lean_ctor_get(v___x_480_, 1);
                v_isSharedCheck_489_ = (!crate::leanh::lean_is_exclusive(v___x_480_)) as u8;
                if v_isSharedCheck_489_ == 0 {
                    v___x_484_ = v___x_480_;
                    v_isShared_485_ = v_isSharedCheck_489_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_482_);
                    crate::leanh::lean_inc(v_fst_481_);
                    crate::leanh::lean_dec(v___x_480_);
                    v___x_484_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fst_481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_482_);
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
    mut v_00_u03b5_490_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_491_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_492_: *mut crate::leanh::LeanObject,
    mut v_x_493_: *mut crate::leanh::LeanObject,
    mut v_s_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_495_ = crate::leanh::lean_apply_1(v_x_493_, v_s_494_);
                v_fst_496_ = crate::leanh::lean_ctor_get(v___x_495_, 0);
                v_snd_497_ = crate::leanh::lean_ctor_get(v___x_495_, 1);
                v_isSharedCheck_504_ = (!crate::leanh::lean_is_exclusive(v___x_495_)) as u8;
                if v_isSharedCheck_504_ == 0 {
                    v___x_499_ = v___x_495_;
                    v_isShared_500_ = v_isSharedCheck_504_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_497_);
                    crate::leanh::lean_inc(v_fst_496_);
                    crate::leanh::lean_dec(v___x_495_);
                    v___x_499_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_503_, 0, v_fst_496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_503_, 1, v_snd_497_);
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
pub unsafe fn runtime_initialize_Init_Control_EState(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_EState(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_EState(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_EState(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_EState(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_EState(builtin);
}
