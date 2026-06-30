// Lean compiler output
// Module: Lake.DSL.Extensions
// Imports: Lean.Environment
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_registerEnvExtension___redArg,
    runtime_initialize_Lean_Environment,
};
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lake_nameExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lake_dirExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lake_optsExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_(
    mut v___x_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_51_, 0, v___x_49_);
    return v___x_51_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed(
    mut v___x_52_: *mut leanh::LeanObject,
    mut v___y_53_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_54_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_(v___x_52_);
    return v_res_54_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_61_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_;
    v___x_62_ = leanh::lean_box(0);
    v___x_63_ = leanh::lean_box(2);
    v___x_64_ = l_Lean_registerEnvExtension___redArg(v___f_61_, v___x_62_, v___x_63_);
    return v___x_64_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed(
    mut v_a_65_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_();
    return v_res_66_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_(
    mut v___x_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_69_, 0, v___x_67_);
    return v___x_69_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed(
    mut v___x_70_: *mut leanh::LeanObject,
    mut v___y_71_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_(v___x_70_);
    return v_res_72_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_76_ = leanh::lean_box(0);
    v___f_77_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_;
    v___x_78_ = leanh::lean_box(2);
    v___x_79_ = l_Lean_registerEnvExtension___redArg(v___f_77_, v___x_76_, v___x_78_);
    return v___x_79_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed(
    mut v_a_80_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_81_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_();
    return v_res_81_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_(
    mut v___x_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_84_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_84_, 0, v___x_82_);
    return v___x_84_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed(
    mut v___x_85_: *mut leanh::LeanObject,
    mut v___y_86_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_87_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_87_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_(v___x_85_);
    return v_res_87_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_91_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_91_ = leanh::lean_box(0);
    v___f_92_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_;
    v___x_93_ = leanh::lean_box(2);
    v___x_94_ = l_Lean_registerEnvExtension___redArg(v___f_92_, v___x_91_, v___x_93_);
    return v___x_94_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed(
    mut v_a_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_96_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_();
    return v_res_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Extensions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_nameExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lake_nameExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_dirExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lake_dirExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_optsExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lake_optsExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Extensions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Extensions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Extensions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Extensions(builtin);
}