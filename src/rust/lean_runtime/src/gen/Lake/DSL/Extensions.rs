// Lean compiler output
// Module: Lake.DSL.Extensions
// Imports: Lean.Environment
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_registerEnvExtension___redArg,
    runtime_initialize_Lean_Environment,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
};
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_(
    mut v___x_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    v___x_51_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_51_, 0, v___x_49_);
    return v___x_51_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed(
    mut v___x_52_: *mut LeanObject,
    mut v___y_53_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_54_: *mut LeanObject = core::ptr::null_mut();
    v_res_54_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_(v___x_52_);
    return v_res_54_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
    v___f_61_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_;
    v___x_62_ = lean_box(0);
    v___x_63_ = lean_box(2);
    v___x_64_ = l_Lean_registerEnvExtension___redArg(v___f_61_, v___x_62_, v___x_63_);
    return v___x_64_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2____boxed(
    mut v_a_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_66_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_();
    return v_res_66_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_(
    mut v___x_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    v___x_69_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_69_, 0, v___x_67_);
    return v___x_69_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed(
    mut v___x_70_: *mut LeanObject,
    mut v___y_71_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_72_: *mut LeanObject = core::ptr::null_mut();
    v_res_72_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_(v___x_70_);
    return v_res_72_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    v___x_76_ = lean_box(0);
    v___f_77_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_;
    v___x_78_ = lean_box(2);
    v___x_79_ = l_Lean_registerEnvExtension___redArg(v___f_77_, v___x_76_, v___x_78_);
    return v___x_79_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2____boxed(
    mut v_a_80_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_81_: *mut LeanObject = core::ptr::null_mut();
    v_res_81_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_();
    return v_res_81_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_(
    mut v___x_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    v___x_84_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_84_, 0, v___x_82_);
    return v___x_84_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed(
    mut v___x_85_: *mut LeanObject,
    mut v___y_86_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_87_: *mut LeanObject = core::ptr::null_mut();
    v_res_87_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_(v___x_85_);
    return v_res_87_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_92_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
    v___x_91_ = lean_box(0);
    v___f_92_ = l___private_Lake_DSL_Extensions_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_;
    v___x_93_ = lean_box(2);
    v___x_94_ = l_Lean_registerEnvExtension___redArg(v___f_92_, v___x_91_, v___x_93_);
    return v___x_94_;
}
pub unsafe fn l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2____boxed(
    mut v_a_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_96_: *mut LeanObject = core::ptr::null_mut();
    v_res_96_ = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_();
    return v_res_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Extensions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_855666303____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_nameExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_nameExt);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_4018895451____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_dirExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_dirExt);
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Extensions_0__Lake_initFn_00___x40_Lake_DSL_Extensions_3376486231____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lake_optsExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lake_optsExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Extensions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Extensions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_Extensions(builtin);
}
