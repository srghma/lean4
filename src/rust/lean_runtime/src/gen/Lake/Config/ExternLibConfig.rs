// Lean compiler output
// Module: Lake.Config.ExternLibConfig
// Imports: Lake.Build.Job.Basic
use crate::r#gen::Lake::Build::Job::Basic::{
    initialize_Lake_Build_Job_Basic, l_Lake_instInhabitedJobState_default,
    runtime_initialize_Lake_Build_Job_Basic,
};
use crate::lean_imports_rs::Init::Core::lean_task_pure;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_unsigned_to_nat,
};
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedExternLibConfig_default___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedExternLibConfig_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedExternLibConfig_default___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    v___x_29_ = l_Lake_instInhabitedJobState_default;
    v___x_30_ = lean_unsigned_to_nat(0);
    v___x_31_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_31_, 0, v___x_30_);
    lean_ctor_set(v___x_31_, 1, v___x_29_);
    return v___x_31_;
}
pub unsafe fn _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    v___x_32_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_35_: u8 = 0;
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    v___x_35_ = 0;
    v___x_36_ = l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__2;
    v___x_37_ = lean_box(0);
    v___x_38_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1_once
        ),
        _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__1,
    );
    v___x_39_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_39_, 0, v___x_38_);
    lean_ctor_set(v___x_39_, 1, v___x_37_);
    lean_ctor_set(v___x_39_, 2, v___x_36_);
    lean_ctor_set_uint8(
        v___x_39_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_35_,
    );
    return v___x_39_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default___lam__0(
    mut v_x_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    v___x_41_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3),
        core::ptr::addr_of_mut!(
            l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3_once
        ),
        _init_l_Lake_instInhabitedExternLibConfig_default___lam__0___closed__3,
    );
    return v___x_41_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default___lam__0___boxed(
    mut v_x_42_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_43_: *mut LeanObject = core::ptr::null_mut();
    v_res_43_ = l_Lake_instInhabitedExternLibConfig_default___lam__0(v_x_42_);
    lean_dec_ref(v_x_42_);
    return v_res_43_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default(
    mut v_pkgName_45_: *mut LeanObject,
    mut v_name_46_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_47_: *mut LeanObject = core::ptr::null_mut();
    v___f_47_ = l_Lake_instInhabitedExternLibConfig_default___closed__0;
    return v___f_47_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig_default___boxed(
    mut v_pkgName_48_: *mut LeanObject,
    mut v_name_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_50_: *mut LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Lake_instInhabitedExternLibConfig_default(v_pkgName_48_, v_name_49_);
    lean_dec(v_name_49_);
    lean_dec(v_pkgName_48_);
    return v_res_50_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig(
    mut v_a_51_: *mut LeanObject,
    mut v_a_52_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_53_: *mut LeanObject = core::ptr::null_mut();
    v___f_53_ = l_Lake_instInhabitedExternLibConfig_default___closed__0;
    return v___f_53_;
}
pub unsafe fn l_Lake_instInhabitedExternLibConfig___boxed(
    mut v_a_54_: *mut LeanObject,
    mut v_a_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_56_: *mut LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Lake_instInhabitedExternLibConfig(v_a_54_, v_a_55_);
    lean_dec(v_a_55_);
    lean_dec(v_a_54_);
    return v_res_56_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_ExternLibConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Job_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_ExternLibConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_ExternLibConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Job_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_ExternLibConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_ExternLibConfig(builtin);
}
