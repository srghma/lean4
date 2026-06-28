// Lean compiler output
// Module: Init.System.Promise
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::lean_imports_rs::Init::Core::lean_task_map;
use crate::lean_imports_rs::Init::System::IO::lean_io_get_task_state;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub static mut l___private_Init_System_Promise_0__IO_PromisePointed: *mut LeanObject =
    core::ptr::null_mut();
pub static l_IO_Promise_result_x21___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_IO_Promise_result_x21___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_Promise_result_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Promise_result_x21___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Init_System_Promise_0__IO_PromisePointed() -> *mut LeanObject {
    let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
    v___x_66_ = lean_box(0);
    return v___x_66_;
}
pub unsafe fn l_IO_Promise_new___boxed(
    mut v_00_u03b1_70_: *mut LeanObject,
    mut v_inst_00___x40_Init_System_Promise_64347732____hygCtx___hyg_71_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_72_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_73_: *mut LeanObject = core::ptr::null_mut();
    v_res_73_ = lean_io_promise_new();
    return v_res_73_;
}
pub unsafe fn l_IO_Promise_resolve___boxed(
    mut v_00_u03b1_78_: *mut LeanObject,
    mut v_value_79_: *mut LeanObject,
    mut v_promise_80_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_82_: *mut LeanObject = core::ptr::null_mut();
    v_res_82_ = lean_io_promise_resolve(v_value_79_, v_promise_80_);
    lean_dec(v_promise_80_);
    return v_res_82_;
}
pub unsafe fn l_IO_Promise_result_x3f___boxed(
    mut v_00_u03b1_85_: *mut LeanObject,
    mut v_promise_86_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_87_: *mut LeanObject = core::ptr::null_mut();
    v_res_87_ = lean_io_promise_result_opt(v_promise_86_);
    lean_dec(v_promise_86_);
    return v_res_87_;
}
pub unsafe fn l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(
    mut v_00_u03b1_91_: *mut LeanObject,
    mut v_inst_00___x40_Init_System_Promise_1729115947____hygCtx___hyg_92_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = lean_option_get_or_block(v_a_00___x40___internal___hyg_93_);
    return v_res_94_;
}
pub unsafe fn l_IO_Promise_result_x21___redArg___lam__0(
    mut v___y_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    v___x_96_ = lean_option_get_or_block(v___y_95_);
    return v___x_96_;
}
pub unsafe fn l_IO_Promise_result_x21___redArg(
    mut v_promise_98_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: u8 = 0;
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    v___f_99_ = l_IO_Promise_result_x21___redArg___closed__0;
    v___x_100_ = lean_io_promise_result_opt(v_promise_98_);
    v___x_101_ = lean_unsigned_to_nat(0);
    v___x_102_ = 1;
    v___x_103_ = lean_task_map(v___f_99_, v___x_100_, v___x_101_, v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_IO_Promise_result_x21___redArg___boxed(
    mut v_promise_104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_105_: *mut LeanObject = core::ptr::null_mut();
    v_res_105_ = l_IO_Promise_result_x21___redArg(v_promise_104_);
    lean_dec(v_promise_104_);
    return v_res_105_;
}
pub unsafe fn l_IO_Promise_result_x21(
    mut v_00_u03b1_106_: *mut LeanObject,
    mut v_promise_107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    v___x_108_ = l_IO_Promise_result_x21___redArg(v_promise_107_);
    return v___x_108_;
}
pub unsafe fn l_IO_Promise_result_x21___boxed(
    mut v_00_u03b1_109_: *mut LeanObject,
    mut v_promise_110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_111_: *mut LeanObject = core::ptr::null_mut();
    v_res_111_ = l_IO_Promise_result_x21(v_00_u03b1_109_, v_promise_110_);
    lean_dec(v_promise_110_);
    return v_res_111_;
}
pub unsafe fn l_IO_Promise_isResolved___redArg(mut v_promise_112_: *mut LeanObject) -> u8 {
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: u8 = 0;
    v___x_114_ = lean_io_promise_result_opt(v_promise_112_);
    v___x_115_ = lean_io_get_task_state(v___x_114_);
    lean_dec_ref(v___x_114_);
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
    mut v_promise_118_: *mut LeanObject,
    mut v_a_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: u8 = 0;
    let mut v_r_121_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l_IO_Promise_isResolved___redArg(v_promise_118_);
    lean_dec(v_promise_118_);
    v_r_121_ = lean_box((v_res_120_) as usize);
    return v_r_121_;
}
pub unsafe fn l_IO_Promise_isResolved(
    mut v_00_u03b1_122_: *mut LeanObject,
    mut v_promise_123_: *mut LeanObject,
) -> u8 {
    let mut v___x_125_: u8 = 0;
    v___x_125_ = l_IO_Promise_isResolved___redArg(v_promise_123_);
    return v___x_125_;
}
pub unsafe fn l_IO_Promise_isResolved___boxed(
    mut v_00_u03b1_126_: *mut LeanObject,
    mut v_promise_127_: *mut LeanObject,
    mut v_a_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_129_: u8 = 0;
    let mut v_r_130_: *mut LeanObject = core::ptr::null_mut();
    v_res_129_ = l_IO_Promise_isResolved(v_00_u03b1_126_, v_promise_127_);
    lean_dec(v_promise_127_);
    v_r_130_ = lean_box((v_res_129_) as usize);
    return v_r_130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_Promise(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Init_System_Promise_0__IO_PromisePointed =
        _init_l___private_Init_System_Promise_0__IO_PromisePointed();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_Promise(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_Promise(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_System_Promise(builtin);
}
