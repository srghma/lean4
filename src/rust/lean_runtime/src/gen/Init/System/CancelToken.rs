// Lean compiler output
// Module: Init.System.CancelToken
// Imports: Init.System.Promise
use crate::r#gen::Init::System::IO::l_BaseIO_chainTask___redArg;
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l_IO_CancelToken_new() -> *mut LeanObject {
    let mut v___x_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_60_: u8 = 0;
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
    v___x_59_ = lean_io_promise_new();
    v___x_60_ = 0;
    v___x_61_ = lean_box((v___x_60_) as usize);
    v___x_62_ = lean_st_mk_ref(v___x_61_);
    v___x_63_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_63_, 0, v___x_59_);
    lean_ctor_set(v___x_63_, 1, v___x_62_);
    return v___x_63_;
}
pub unsafe fn l_IO_CancelToken_new___boxed(mut v_a_64_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_65_: *mut LeanObject = core::ptr::null_mut();
    v_res_65_ = l_IO_CancelToken_new();
    return v_res_65_;
}
pub unsafe fn l_IO_CancelToken_set(mut v_tk_66_: *mut LeanObject) -> *mut LeanObject {
    let mut v_promise_68_: *mut LeanObject = core::ptr::null_mut();
    let mut v_setRef_69_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_72_: u8 = 0;
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
    v_promise_68_ = lean_ctor_get(v_tk_66_, 0);
    v_setRef_69_ = lean_ctor_get(v_tk_66_, 1);
    v___x_70_ = lean_box(0);
    v___x_71_ = lean_io_promise_resolve(v___x_70_, v_promise_68_);
    v___x_72_ = 1;
    v___x_73_ = lean_box((v___x_72_) as usize);
    v___x_74_ = lean_st_ref_set(v_setRef_69_, v___x_73_);
    return v___x_74_;
}
pub unsafe fn l_IO_CancelToken_set___boxed(
    mut v_tk_75_: *mut LeanObject,
    mut v_a_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_77_: *mut LeanObject = core::ptr::null_mut();
    v_res_77_ = l_IO_CancelToken_set(v_tk_75_);
    lean_dec_ref(v_tk_75_);
    return v_res_77_;
}
pub unsafe fn l_IO_CancelToken_isSet(mut v_tk_78_: *mut LeanObject) -> u8 {
    let mut v_setRef_80_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_82_: u8 = 0;
    v_setRef_80_ = lean_ctor_get(v_tk_78_, 1);
    v___x_81_ = lean_st_ref_get(v_setRef_80_);
    v___x_82_ = (lean_unbox(v___x_81_) as u8);
    lean_dec(v___x_81_);
    return v___x_82_;
}
pub unsafe fn l_IO_CancelToken_isSet___boxed(
    mut v_tk_83_: *mut LeanObject,
    mut v_a_84_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_85_: u8 = 0;
    let mut v_r_86_: *mut LeanObject = core::ptr::null_mut();
    v_res_85_ = l_IO_CancelToken_isSet(v_tk_83_);
    lean_dec_ref(v_tk_83_);
    v_r_86_ = lean_box((v_res_85_) as usize);
    return v_r_86_;
}
pub unsafe fn l_IO_CancelToken_onSet___lam__0(
    mut v_action_87_: *mut LeanObject,
    mut v_x_88_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
    v___x_90_ = lean_apply_1(v_action_87_, lean_box(0));
    return v___x_90_;
}
pub unsafe fn l_IO_CancelToken_onSet___lam__0___boxed(
    mut v_action_91_: *mut LeanObject,
    mut v_x_92_: *mut LeanObject,
    mut v___y_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_94_: *mut LeanObject = core::ptr::null_mut();
    v_res_94_ = l_IO_CancelToken_onSet___lam__0(v_action_91_, v_x_92_);
    lean_dec(v_x_92_);
    return v_res_94_;
}
pub unsafe fn l_IO_CancelToken_onSet(
    mut v_tk_95_: *mut LeanObject,
    mut v_action_96_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_promise_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: u8 = 0;
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    v_promise_98_ = lean_ctor_get(v_tk_95_, 0);
    v___f_99_ = lean_alloc_closure(
        l_IO_CancelToken_onSet___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_99_, 0, v_action_96_);
    v___x_100_ = lean_io_promise_result_opt(v_promise_98_);
    v___x_101_ = lean_unsigned_to_nat(0);
    v___x_102_ = 1;
    v___x_103_ = l_BaseIO_chainTask___redArg(v___x_100_, v___f_99_, v___x_101_, v___x_102_);
    return v___x_103_;
}
pub unsafe fn l_IO_CancelToken_onSet___boxed(
    mut v_tk_104_: *mut LeanObject,
    mut v_action_105_: *mut LeanObject,
    mut v_a_106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_107_: *mut LeanObject = core::ptr::null_mut();
    v_res_107_ = l_IO_CancelToken_onSet(v_tk_104_, v_action_105_);
    lean_dec_ref(v_tk_104_);
    return v_res_107_;
}
pub unsafe fn lean_io_cancel_token_is_set(mut v_tk_108_: *mut LeanObject) -> u8 {
    let mut v___x_110_: u8 = 0;
    v___x_110_ = l_IO_CancelToken_isSet(v_tk_108_);
    lean_dec_ref(v_tk_108_);
    return v___x_110_;
}
pub unsafe fn l___private_Init_System_CancelToken_0__IO_CancelToken_isSetExport___boxed(
    mut v_tk_111_: *mut LeanObject,
    mut v_a_112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_113_: u8 = 0;
    let mut v_r_114_: *mut LeanObject = core::ptr::null_mut();
    v_res_113_ = lean_io_cancel_token_is_set(v_tk_111_);
    v_r_114_ = lean_box((v_res_113_) as usize);
    return v_r_114_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_CancelToken(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_CancelToken(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_CancelToken(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_CancelToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_System_CancelToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_System_CancelToken(builtin);
}
