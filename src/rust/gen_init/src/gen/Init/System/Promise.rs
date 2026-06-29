// Lean compiler output
// Module: Init.System.Promise
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::ffi::lean_task_map;
use crate::ffi::lean_io_get_task_state;
use crate::ffi::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
    lean_option_get_or_block,
};
pub static mut l___private_Init_System_Promise_0__IO_PromisePointed: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_IO_Promise_result_x21___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_IO_Promise_result_x21___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_Promise_result_x21___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Promise_result_x21___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Init_System_Promise_0__IO_PromisePointed()
-> *mut crate::leanh::LeanObject {
    let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_66_ = crate::leanh::lean_box(0);
    return v___x_66_;
}
pub unsafe fn l_IO_Promise_new___boxed(
    mut v_00_u03b1_70_: *mut crate::leanh::LeanObject,
    mut v_inst_00___x40_Init_System_Promise_64347732____hygCtx___hyg_71_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_72_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_73_ = lean_io_promise_new();
    return v_res_73_;
}
pub unsafe fn l_IO_Promise_resolve___boxed(
    mut v_00_u03b1_78_: *mut crate::leanh::LeanObject,
    mut v_value_79_: *mut crate::leanh::LeanObject,
    mut v_promise_80_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_81_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_82_ = lean_io_promise_resolve(v_value_79_, v_promise_80_);
    crate::leanh::lean_dec(v_promise_80_);
    return v_res_82_;
}
pub unsafe fn l_IO_Promise_result_x3f___boxed(
    mut v_00_u03b1_85_: *mut crate::leanh::LeanObject,
    mut v_promise_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_87_ = lean_io_promise_result_opt(v_promise_86_);
    crate::leanh::lean_dec(v_promise_86_);
    return v_res_87_;
}
pub unsafe fn l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(
    mut v_00_u03b1_91_: *mut crate::leanh::LeanObject,
    mut v_inst_00___x40_Init_System_Promise_1729115947____hygCtx___hyg_92_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = lean_option_get_or_block(v_a_00___x40___internal___hyg_93_);
    return v_res_94_;
}
pub unsafe fn l_IO_Promise_result_x21___redArg___lam__0(
    mut v___y_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = lean_option_get_or_block(v___y_95_);
    return v___x_96_;
}
pub unsafe fn l_IO_Promise_result_x21___redArg(
    mut v_promise_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: u8 = 0;
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_99_ = l_IO_Promise_result_x21___redArg___closed__0;
    v___x_100_ = lean_io_promise_result_opt(v_promise_98_);
    v___x_101_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_102_ = 1;
    v___x_103_ = lean_task_map(v___f_99_, v___x_100_, v___x_101_, v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_IO_Promise_result_x21___redArg___boxed(
    mut v_promise_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_105_ = l_IO_Promise_result_x21___redArg(v_promise_104_);
    crate::leanh::lean_dec(v_promise_104_);
    return v_res_105_;
}
pub unsafe fn l_IO_Promise_result_x21(
    mut v_00_u03b1_106_: *mut crate::leanh::LeanObject,
    mut v_promise_107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_108_ = l_IO_Promise_result_x21___redArg(v_promise_107_);
    return v___x_108_;
}
pub unsafe fn l_IO_Promise_result_x21___boxed(
    mut v_00_u03b1_109_: *mut crate::leanh::LeanObject,
    mut v_promise_110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_111_ = l_IO_Promise_result_x21(v_00_u03b1_109_, v_promise_110_);
    crate::leanh::lean_dec(v_promise_110_);
    return v_res_111_;
}
pub unsafe fn l_IO_Promise_isResolved___redArg(
    mut v_promise_112_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: u8 = 0;
    v___x_114_ = lean_io_promise_result_opt(v_promise_112_);
    v___x_115_ = lean_io_get_task_state(v___x_114_);
    crate::leanh::lean_dec_ref(v___x_114_);
    if v___x_115_ == 2 {
        let mut v___x_116_: u8 = 0;
        v___x_116_ = 1;
        return v___x_116_;
    } else {
        let mut v___x_117_: u8 = 0;
        v___x_117_ = 0;
        return v___x_117_;
    }
}
pub unsafe fn l_IO_Promise_isResolved___redArg___boxed(
    mut v_promise_118_: *mut crate::leanh::LeanObject,
    mut v_a_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_120_: u8 = 0;
    let mut v_r_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l_IO_Promise_isResolved___redArg(v_promise_118_);
    crate::leanh::lean_dec(v_promise_118_);
    v_r_121_ = crate::leanh::lean_box((v_res_120_) as usize);
    return v_r_121_;
}
pub unsafe fn l_IO_Promise_isResolved(
    mut v_00_u03b1_122_: *mut crate::leanh::LeanObject,
    mut v_promise_123_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_125_: u8 = 0;
    v___x_125_ = l_IO_Promise_isResolved___redArg(v_promise_123_);
    return v___x_125_;
}
pub unsafe fn l_IO_Promise_isResolved___boxed(
    mut v_00_u03b1_126_: *mut crate::leanh::LeanObject,
    mut v_promise_127_: *mut crate::leanh::LeanObject,
    mut v_a_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_129_: u8 = 0;
    let mut v_r_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_129_ = l_IO_Promise_isResolved(v_00_u03b1_126_, v_promise_127_);
    crate::leanh::lean_dec(v_promise_127_);
    v_r_130_ = crate::leanh::lean_box((v_res_129_) as usize);
    return v_r_130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_Promise(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Init_System_Promise_0__IO_PromisePointed =
        _init_l___private_Init_System_Promise_0__IO_PromisePointed();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_Promise(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_Promise(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_System_Promise(builtin);
}
