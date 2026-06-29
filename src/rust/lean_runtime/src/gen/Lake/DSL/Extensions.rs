// Lean compiler output
// Module: Lake.DSL.Extensions
// Imports: Lean.Environment
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_registerEnvExtension___redArg,
    runtime_initialize_Lean_Environment,
};
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_nameExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_dirExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_optsExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_(
    mut v___x_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_51_, 0, v___x_49_);
    return v___x_51_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed(
    mut v___x_52_: *mut crate::leanh::LeanObject,
    mut v___y_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_54_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_(v___x_52_);
    return v_res_54_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_61_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_;
    v___x_62_ = crate::leanh::lean_box(0);
    v___x_63_ = crate::leanh::lean_box(2);
    v___x_64_ = l_Lean_registerEnvExtension___redArg(v___f_61_, v___x_62_, v___x_63_);
    return v___x_64_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed(
    mut v_a_65_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_();
    return v_res_66_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_(
    mut v___x_67_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_69_, 0, v___x_67_);
    return v___x_69_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed(
    mut v___x_70_: *mut crate::leanh::LeanObject,
    mut v___y_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_72_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_(v___x_70_);
    return v_res_72_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_76_ = crate::leanh::lean_box(0);
    v___f_77_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_;
    v___x_78_ = crate::leanh::lean_box(2);
    v___x_79_ = l_Lean_registerEnvExtension___redArg(v___f_77_, v___x_76_, v___x_78_);
    return v___x_79_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed(
    mut v_a_80_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_81_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_();
    return v_res_81_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_(
    mut v___x_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_84_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_84_, 0, v___x_82_);
    return v___x_84_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed(
    mut v___x_85_: *mut crate::leanh::LeanObject,
    mut v___y_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_87_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_(v___x_85_);
    return v_res_87_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_91_ = crate::leanh::lean_box(0);
    v___f_92_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_;
    v___x_93_ = crate::leanh::lean_box(2);
    v___x_94_ = l_Lean_registerEnvExtension___redArg(v___f_92_, v___x_91_, v___x_93_);
    return v___x_94_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed(
    mut v_a_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_96_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_();
    return v_res_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Extensions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_nameExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_nameExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_dirExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_dirExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_optsExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lake_optsExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Extensions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Extensions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Extensions(builtin);
}
