// Lean compiler output
// Module: Lake.Config.ExternLibConfig
// Imports: Lake.Build.Job.Basic
use crate::ffi::lean_task_pure;
use crate::r#gen::Lake::Build::Job::Basic::{
    initialize_Lake_Build_Job_Basic, l_Lake_instInhabitedJobState_default,
    runtime_initialize_Lake_Build_Job_Basic,
};
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedExternLibConfig_default___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedExternLibConfig_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedExternLibConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_29_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_29_ = l_Lake_instInhabitedJobState_default;
    v___x_30_ = leanh::lean_unsigned_to_nat(0);
    v___x_31_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_31_, 0, v___x_30_);
    leanh::lean_ctor_set(v___x_31_, 1, v___x_29_);
    return v___x_31_;
}
pub unsafe fn _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_32_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0_once
        ),
        _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0,
    );
    v___x_33_ = lean_task_pure(v___x_32_);
    return v___x_33_;
}
pub unsafe fn _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_35_: u8 = 0;
    let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_35_ = 0;
    v___x_36_ = l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2;
    v___x_37_ = leanh::lean_box(0);
    v___x_38_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1_once
        ),
        _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1,
    );
    v___x_39_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_39_, 0, v___x_38_);
    leanh::lean_ctor_set(v___x_39_, 1, v___x_37_);
    leanh::lean_ctor_set(v___x_39_, 2, v___x_36_);
    leanh::lean_ctor_set_uint8(
        v___x_39_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_35_,
    );
    return v___x_39_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default___lam__0(
    mut v_x_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3_once
        ),
        _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3,
    );
    return v___x_41_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed(
    mut v_x_42_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_43_ = l_Lake_instInhabitedExternLibConfig_default___lam__0(v_x_42_);
    leanh::lean_dec_ref(v_x_42_);
    return v_res_43_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default(
    mut v_pkgName_45_: *mut leanh::LeanObject,
    mut v_name_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_47_ = l_Lake_instInhabitedExternLibConfig_default___closed__0;
    return v___f_47_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default___boxed(
    mut v_pkgName_48_: *mut leanh::LeanObject,
    mut v_name_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Lake_instInhabitedExternLibConfig_default(v_pkgName_48_, v_name_49_);
    leanh::lean_dec(v_name_49_);
    leanh::lean_dec(v_pkgName_48_);
    return v_res_50_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig(
    mut v_a_51_: *mut leanh::LeanObject,
    mut v_a_52_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_53_ = l_Lake_instInhabitedExternLibConfig_default___closed__0;
    return v___f_53_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig___boxed(
    mut v_a_54_: *mut leanh::LeanObject,
    mut v_a_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Lake_instInhabitedExternLibConfig(v_a_54_, v_a_55_);
    leanh::lean_dec(v_a_55_);
    leanh::lean_dec(v_a_54_);
    return v_res_56_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ExternLibConfig(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Job_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ExternLibConfig(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_ExternLibConfig(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Job_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLibConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ExternLibConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_ExternLibConfig(builtin);
}